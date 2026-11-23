module

public import RBM8D.Graph.QExp.PStepsPart1
import all RBM8D.Graph.QExp.PStepsPart1

@[expose] public section

/-!
# The `P`-graph step of the `Q`-expansions

[II, Lemma 4.13], with [II, (4.23), (4.24)].
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs
/-! ## The graphs of the multi-edge expansion, case (iii) -/

section InDefs

variable {k n : ℕ} (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ) (e₁ : Comp (Atom k n))

/-- The indices of the solid edges entering `x`, in the order of case (iii). -/
def psteps_iXIdx : List ℕ := Γ.edgeIdx x .plus false ++ Γ.edgeIdx x .minus false

/-- The solid edge `G_{w₁ α}`. -/
def PS_iGw : Comp (Atom k (n + 1)) := mkC (.G .plus) (liftA 1 e₁.x) (newA 0)

/-- A main term of [I, (3.14)] for the edge `Ḡ_{w' x}` at position `j`: the components other than
`G_{w₁ x}` and `Ḡ_{w' x}`, and `s_{xα} G_{w₁ α} Ḡ_{w' α}`. -/
def PS_iBaseM (j : ℕ) : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
    [PS_oSx x, PS_iGw e₁, mkC (.G .minus) (liftA 1 ((Γ.comps.getD j e₁).x)) (newA 0)]

/-- The `(k₃ - 1)` term of [I, (3.14)]: the components other than `G_{w₁ x}`, and
`s_{xα} G_{w₁ α} G_{αx}`. -/
def PS_iE1 : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (Γ.comps.eraseIdx i₁) ++ [PS_oSx x, PS_iGw e₁, mkC (.G .plus) (newA 0) (liftA 1 x)]

/-- The derivative terms of [I, (3.14)]: the edges entering `x` other than `G_{w₁ x}`, one graph of
`-∂_{h_{xα}}` of the other components, and `s_{xα} G_{w₁ α}`. -/
def PS_iDs : List (List (Comp (Atom k (n + 1)))) :=
  (dTerms (liftA 1 x) (newA 0) (liftCs 1 (eraseIdxs (psteps_iXIdx x Γ) Γ.comps))).map fun d =>
    liftCs 1 (pickIdxs ((psteps_iXIdx x Γ).filter (· != i₁)) Γ.comps) ++ d ++ [PS_oSx x, PS_iGw e₁]

/-- The formal sum of `multiEIn`. -/
def psteps_iOut : TExpansion k n :=
  (Γ.edgeIdx x .minus false).map (fun j => PS_t1 (PS_iBaseM x Γ i₁ e₁ j) (cm * cmb * Γ.coeff)) ++
    (Γ.edgeIdx x .minus false).map (fun j => PS_t1 (PS_iBaseM x Γ i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) (cm * Γ.coeff)) ++
    [PS_t1 (PS_oL3 x Γ) (cm * Γ.coeff)] ++
    (if is₂.isEmpty then [] else [PS_t1 (PS_iE1 x Γ i₁ e₁) ((is₂.length : Coeff) * cm * Γ.coeff)]) ++
    (PS_iDs x Γ i₁ e₁).map (fun d => PS_t1 d (cm * Γ.coeff)) ++
    [⟨n, ⟨labelQs x Γ.comps, Γ.coeff⟩, id⟩] ++
    (Γ.edgeIdx x .minus false).map (fun j => PS_t1 (labelQs (liftA 1 x) (PS_iBaseM x Γ i₁ e₁ j ++
      [mkC (.weight .minus) (liftA 1 x) (liftA 1 x)])) (-cm * Γ.coeff)) ++
    [PS_t1 (labelQs (liftA 1 x) (PS_oL3 x Γ)) (-cm * Γ.coeff)] ++
    (if is₂.isEmpty then [] else
      [PS_t1 (labelQs (liftA 1 x) (PS_iE1 x Γ i₁ e₁)) (-(is₂.length : Coeff) * cm * Γ.coeff)]) ++
    (PS_iDs x Γ i₁ e₁).map (fun d => PS_t1 (labelQs (liftA 1 x) d) (-cm * Γ.coeff))

theorem multiEIn_some {E : TExpansion k n} (h : multiEIn x Γ = some E) :
    ∃ i₁ is₂ e₁, Γ.edgeIdx x .plus false = i₁ :: is₂ ∧ Γ.comps[i₁]? = some e₁ ∧
      Γ.xdotsAt x (psteps_iXIdx x Γ) = true ∧ E = psteps_iOut x Γ i₁ is₂ e₁ := by
  unfold multiEIn at h
  split at h
  · exact absurd h (by simp)
  rename_i i₁ is₂ hIP
  split at h
  · exact absurd h (by simp)
  rename_i e₁ hL
  dsimp only at h
  rw [ite_eq_iff] at h
  rcases h with ⟨_, h⟩ | ⟨hX, h⟩
  · exact absurd h (by simp)
  refine ⟨i₁, is₂, e₁, hIP, hL, by simpa [psteps_iXIdx] using hX, ?_⟩
  exact (Option.some.inj h).symm

end InDefs

section InPos

variable {k n : ℕ} (x : Atom k n)

/-- The component at a position is a solid edge entering `x` (self-loops excluded). -/
def cI (p : Comp (Atom k n) × ℕ) : Bool := ep x .plus false p || ep x .minus false p

theorem cI_random {p : Comp (Atom k n) × ℕ} (h : cI x p = true) :
    p.1.kind.isRandom = true := by
  unfold cI at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h <;> rw [(ep_spec x h).1] <;> rfl

theorem contains_iXIdx (Γ : Graph k n) {p : Comp (Atom k n) × ℕ}
    (hp : p ∈ Γ.comps.zipIdx) : (psteps_iXIdx x Γ).contains p.2 = cI x p := by
  simp only [psteps_iXIdx, edgeIdx_eq, List.contains_append, contains_filter_snd hp, cI]

end InPos

section InProd

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k n : ℕ} {x : Atom k n} {Γ : Graph k n}
  {i₁ : ℕ} (σ : Atom k n → ι) {is₂ : List ℕ} {e₁ : Comp (Atom k n)}

omit [Fintype ι] [DecidableEq ι] in
theorem in_hxI : ∀ p ∈ Γ.comps.zipIdx, (psteps_iXIdx x Γ).contains p.2 = cI x p :=
  fun _ hp => contains_iXIdx x Γ hp

theorem in_hcR : ∀ p : Comp (Atom k n) × ℕ, cI x p = true → p.1.kind.isRandom = true :=
  fun _ h => cI_random x h

variable (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂) (hL : Γ.comps[i₁]? = some e₁)
include hIP hL

omit [Fintype ι] [DecidableEq ι] in
theorem in_e₁_ep : ep x .plus false (e₁, i₁) = true := by
  have h : i₁ ∈ Γ.edgeIdx x .plus false := by rw [hIP]; exact List.mem_cons_self ..
  rw [edgeIdx_eq] at h
  exact (mem_filter_snd (mem_zip_of_get hL)).1 h

omit [Fintype ι] [DecidableEq ι] in
theorem in_e₁_cI : cI x (e₁, i₁) = true := by
  simp [cI, in_e₁_ep hIP hL]

theorem in_R1 (D₀ : Data ι) :
    rv D₀ σ Γ.comps = Comp.val D₀ σ e₁ *
      (Kx (cI x) Γ i₁ σ D₀ * rv D₀ σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps)) :=
  gR1 σ in_hxI in_hcR (mem_zip_of_get hL) (in_e₁_cI hIP hL) D₀

theorem in_R2 (D₀ : Data ι) :
    rv D₀ σ (Γ.comps.eraseIdx i₁) =
      Kx (cI x) Γ i₁ σ D₀ * rv D₀ σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps) :=
  gR2 σ in_hxI in_hcR (mem_zip_of_get hL) (in_e₁_cI hIP hL) D₀

theorem in_R3 (D₀ : Data ι) {q : Comp (Atom k n) × ℕ} (hq : q ∈ Γ.comps.zipIdx)
    (hqc : cI x q = true) :
    rv D₀ σ (eraseIdxs [i₁, q.2] Γ.comps) =
      Kxq (cI x) Γ i₁ σ D₀ q.2 * rv D₀ σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps) :=
  gR3 σ in_hxI in_hcR (mem_zip_of_get hL) (in_e₁_cI hIP hL) D₀ hq hqc

theorem in_D1 (D₀ : Data ι) : dv D₀ σ (Γ.comps.eraseIdx i₁) = dv D₀ σ Γ.comps :=
  gD1 σ in_hcR (mem_zip_of_get hL) (in_e₁_cI hIP hL) D₀

theorem in_D3 (D₀ : Data ι) {q : Comp (Atom k n) × ℕ} (hq : q ∈ Γ.comps.zipIdx)
    (hqc : cI x q = true) : dv D₀ σ (eraseIdxs [i₁, q.2] Γ.comps) = dv D₀ σ Γ.comps :=
  gD3 σ in_hcR (mem_zip_of_get hL) (in_e₁_cI hIP hL) D₀ hq hqc

omit hIP hL in
theorem in_R4 (D₀ : Data ι) :
    rv D₀ σ (pickIdxs ((psteps_iXIdx x Γ).filter (· != i₁)) Γ.comps) = Kx (cI x) Γ i₁ σ D₀ :=
  gR4 σ in_hxI in_hcR D₀

omit hIP hL in
theorem in_D4 (D₀ : Data ι) :
    dv D₀ σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps) = dv D₀ σ Γ.comps :=
  gD4 σ in_hxI in_hcR D₀

omit hIP hL in
theorem in_D5 (D₀ : Data ι) :
    dv D₀ σ (pickIdxs ((psteps_iXIdx x Γ).filter (· != i₁)) Γ.comps) = 1 :=
  gD5 σ in_hxI in_hcR D₀

end InProd

section InDeriv

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ} {x : Atom k n} {Γ : Graph k n} (σ : Atom k n → ι)

theorem dh_IPx {p : Comp (Atom k n) × ℕ} (hc : p.1.isPlainB = true)
    (h : ep x .plus false p = true) (β : ι) :
    A.dh (σ x) β (fun ω => Comp.val (D ω) σ p.1) =
      fun ω => -(Comp.val (D ω) σ p.1 * A.G ω β (σ x)) := by
  obtain ⟨hk, -, hi⟩ := ep_spec x h
  rw [fun_edge A σ hc hk]
  simp only [Charge.apply, dh_G', (hi rfl).1, val_edge A σ hc hk]

theorem dh_IMx {p : Comp (Atom k n) × ℕ} (hc : p.1.isPlainB = true)
    (h : ep x .minus false p = true) (β : ι) :
    A.dh (σ x) β (fun ω => Comp.val (D ω) σ p.1) =
      fun ω => -(star (A.G ω (σ p.1.x) β) * star (A.G ω (σ x) (σ x))) := by
  obtain ⟨hk, -, hi⟩ := ep_spec x h
  rw [fun_edge A σ hc hk]
  simp only [Charge.apply, dh_starG', (hi rfl).1]

/-- The term of `-∂_{h_{xβ}}` at one position, times the other factors, sorted into the
families of [I, (3.14)]. -/
theorem in_PP (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) {p : Comp (Atom k n) × ℕ} (hp : p ∈ Γ.comps.zipIdx)
    (β : ι) (ω : Ω) :
    -(A.dh (σ x) β (fun ω => kx (cI x) i₁ σ (D ω) p) ω) * Kxq (cI x) Γ i₁ σ (D ω) p.2 *
        rv (D ω) σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps) * A.G ω (σ e₁.x) β =
      (if ep x .minus false p = true then rv (D ω) σ (eraseIdxs [i₁, p.2] Γ.comps) *
          (A.G ω (σ e₁.x) β * star (A.G ω (σ (Γ.comps.getD p.2 e₁).x) β)) *
          star (A.G ω (σ x) (σ x)) else 0) +
      (if (ep x .plus false p && p.2 != i₁) = true then rv (D ω) σ (Γ.comps.eraseIdx i₁) *
          (A.G ω (σ e₁.x) β * A.G ω β (σ x)) else 0) := by
  have hplp := hpl _ (fst_mem_of_zip hp)
  rw [dh_kx A σ (cI x) i₁ p]
  by_cases hb : (cI x p && p.2 != i₁) = true
  · rw [ite_eq_left hb]
    obtain ⟨hc, hne⟩ := Bool.and_eq_true_iff.1 hb
    have hK := Kx_single (cI x) Γ i₁ σ (D ω) hp
    rw [kx, ite_eq_left hb] at hK
    have hgd := getD_of_zip hp e₁
    simp only [cI, Bool.or_eq_true] at hc
    rcases hc with h | h
    · rw [dh_IPx A σ hplp h, in_R2 σ hIP hL, hK,
        ep_false h (ch' := .minus) (out' := false) (by simp)]
      simp only [h, hne, Bool.and_self, ite_true, Bool.false_eq_true, ite_false]
      ring
    · rw [dh_IMx A σ hplp h, in_R3 σ hIP hL (D ω) hp (by simp [cI, h]), hgd,
        ep_false h (ch' := .plus) (out' := false) (by simp)]
      simp only [h, ite_true, Bool.false_eq_true, ite_false, Bool.false_and]
      ring
  · rw [ite_eq_right hb]
    have h1 : ep x .minus false p = false := by
      by_contra h
      have h' : ep x .minus false p = true := by simpa using h
      apply hb
      rw [show cI x p = true by simp [cI, h'], Bool.true_and]
      by_contra h2
      have := zip_eq_of_snd hp (mem_zip_of_get hL) (by simpa using h2)
      subst this
      exact absurd (ep_excl x h' (in_e₁_ep hIP hL)).1 (by simp)
    have h4 : (ep x .plus false p && p.2 != i₁) = false := by
      by_contra h
      have h' : (ep x .plus false p && p.2 != i₁) = true := by simpa using h
      obtain ⟨h5, h6⟩ := Bool.and_eq_true_iff.1 h'
      exact hb (by rw [show cI x p = true by simp [cI, h5], h6]; rfl)
    simp [h1, h4]

omit [Fintype ι] [DecidableEq ι] in
theorem len_IP {i₁ : ℕ} {is₂ : List ℕ} (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂) :
    (Γ.comps.zipIdx.filter fun p => ep x .plus false p && p.2 != i₁).length = is₂.length := by
  have hnd : (i₁ :: is₂).Nodup := by
    rw [← hIP, edgeIdx_eq]
    exact (zip_snd_nodup Γ.comps).sublist ((List.filter_sublist).map _)
  have h : ((Γ.comps.zipIdx.filter fun p => ep x .plus false p && p.2 != i₁).map Prod.snd) =
      is₂ := by
    have e1 : (Γ.comps.zipIdx.filter fun p => ep x .plus false p && p.2 != i₁) =
        (Γ.comps.zipIdx.filter (ep x .plus false)).filter (fun p => p.2 != i₁) := by
      rw [List.filter_filter]
      congr 1
      funext p
      exact Bool.and_comm _ _
    have e2 : ((Γ.comps.zipIdx.filter (ep x .plus false)).filter (fun p => p.2 != i₁)).map
        Prod.snd = ((Γ.comps.zipIdx.filter (ep x .plus false)).map Prod.snd).filter (· != i₁) := by
      rw [List.filter_map]
      rfl
    rw [e1, e2, ← edgeIdx_eq, hIP]
    rw [List.filter_cons_of_neg (by simp), List.filter_eq_self.2]
    intro a ha
    have : a ≠ i₁ := fun h => (List.nodup_cons.1 hnd).1 (h ▸ ha)
    simpa using this
  rw [← h, List.length_map]

/-- `G_{w₁ β}` times `-∂_{h_{xβ}}` of the product of the edges entering `x` other than
`G_{w₁ x}` and of the rest: the families of [I, (3.14)] and the derivative terms. -/
theorem in_KEY (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (σ' : Atom k (n + 1) → ι) (hσ' : σ' ∘ liftA 1 = σ)
    (β : ι) (hβ : σ' (newA 0) = β) (ω : Ω) :
    A.G ω (σ e₁.x) β * -(A.dh (σ x) β (fun ω' => Kx (cI x) Γ i₁ σ (D ω') *
        rv (D ω') σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps)) ω) =
      ((Γ.edgeIdx x .minus false).map fun j => rv (D ω) σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω (σ e₁.x) β * star (A.G ω (σ (Γ.comps.getD j e₁).x) β)) *
          star (A.G ω (σ x) (σ x))).sum +
      (is₂.length : ℂ) * (rv (D ω) σ (Γ.comps.eraseIdx i₁) * (A.G ω (σ e₁.x) β * A.G ω β (σ x))) +
      ((PS_iDs x Γ i₁ e₁).map fun d => rv (D ω) σ' d).sum := by
  have hKt : A.Test fun ω' => Kx (cI x) Γ i₁ σ (D ω') :=
    test_listProd' A _ fun p hp => kx_test A σ hpl in_hcR i₁ hp
  have hFb : ∀ c ∈ eraseIdxs (psteps_iXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  have hFt : A.Test fun ω' => rv (D ω') σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps) :=
    rv_test A σ _ fun c hc => (basB_of_plain (hFb c hc)).1
  have hdK : A.dh (σ x) β (fun ω' => Kx (cI x) Γ i₁ σ (D ω')) = fun ω' =>
      (Γ.comps.zipIdx.map fun p => A.dh (σ x) β (fun ω'' => kx (cI x) i₁ σ (D ω'') p) ω' *
        Kxq (cI x) Γ i₁ σ (D ω') p.2).sum :=
    dh_prod_rule A (σ x) β Prod.snd _ (zip_snd_nodup _) (fun p ω => kx (cI x) i₁ σ (D ω) p)
      (fun p hp => kx_test A σ hpl in_hcR i₁ hp)
  have hdF := (dTerms_spec A σ' (liftA 1 x) (newA 0) _ (plain_bas_lift hFb 1)).2 ω
  simp only [rv_liftCs, hσ', hβ] at hdF
  rw [show σ' (liftA 1 x) = σ x by rw [← hσ']; rfl] at hdF
  have hD : ((PS_iDs x Γ i₁ e₁).map fun d => rv (D ω) σ' d).sum =
      Kx (cI x) Γ i₁ σ (D ω) * A.G ω (σ e₁.x) β *
        ((dTerms (liftA 1 x) (newA 0) (liftCs 1 (eraseIdxs (psteps_iXIdx x Γ) Γ.comps))).map
          fun d => rv (D ω) σ' d).sum := by
    rw [PS_iDs, List.map_map, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun d _ => ?_)
    simp only [Function.comp_apply, rv_append, rv_liftCs, hσ', in_R4, PS_oSx, PS_iGw, rv_cons,
      rv_nil, mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      Charge.apply, one_mul, mul_one, hβ]
    rw [show σ' (liftA 1 e₁.x) = σ e₁.x by rw [← hσ']; rfl]
    ring
  rw [dh_mul' A (σ x) β hKt hFt, hD, hdF, hdK]
  have hPP : ∀ p ∈ Γ.comps.zipIdx,
      -(A.dh (σ x) β (fun ω => kx (cI x) i₁ σ (D ω) p) ω) * Kxq (cI x) Γ i₁ σ (D ω) p.2 *
        rv (D ω) σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps) * A.G ω (σ e₁.x) β = _ :=
    fun p hp => in_PP A σ hpl hIP hL hp β ω
  have hsum : A.G ω (σ e₁.x) β * -((Γ.comps.zipIdx.map fun p =>
        A.dh (σ x) β (fun ω'' => kx (cI x) i₁ σ (D ω'') p) ω * Kxq (cI x) Γ i₁ σ (D ω) p.2).sum *
        rv (D ω) σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps)) =
      (Γ.comps.zipIdx.map fun p => -(A.dh (σ x) β (fun ω => kx (cI x) i₁ σ (D ω) p) ω) *
        Kxq (cI x) Γ i₁ σ (D ω) p.2 * rv (D ω) σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps) *
        A.G ω (σ e₁.x) β).sum := by
    rw [← List.sum_map_mul_right, ← list_sum_neg, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    ring
  rw [List.map_congr_left hPP] at hsum
  simp only [List.sum_map_add] at hsum
  have h1 := sum_filter_snd Γ.comps.zipIdx (ep x .minus false) (fun j =>
    rv (D ω) σ (eraseIdxs [i₁, j] Γ.comps) *
      (A.G ω (σ e₁.x) β * star (A.G ω (σ (Γ.comps.getD j e₁).x) β)) * star (A.G ω (σ x) (σ x)))
  have h3 := sum_ite_const Γ.comps.zipIdx (fun p => ep x .plus false p && p.2 != i₁)
    (rv (D ω) σ (Γ.comps.eraseIdx i₁) * (A.G ω (σ e₁.x) β * A.G ω β (σ x)))
  rw [len_IP hIP] at h3
  rw [← edgeIdx_eq] at h1
  simp only []
  linear_combination hsum - h1 + h3

/-- Linearity of `P_x` on a sum of the shape of [I, (3.14)]. -/
theorem P_lin3 {γ : Type*} (X : ι) (l₁ : List ℕ) (l₅ : List γ) (f₁ : ℕ → Ω → ℂ)
    (f₅ : γ → Ω → ℂ) (c₃ : ℂ) (g₃ : Ω → ℂ) (h₁ : ∀ j ∈ l₁, A.Good (f₁ j)) (h₃ : A.Good g₃)
    (h₅ : ∀ d ∈ l₅, A.Good (f₅ d)) (ω : Ω) :
    PF.P X (fun ω' => (l₁.map fun j => f₁ j ω').sum + c₃ * g₃ ω' +
        (l₅.map fun d => f₅ d ω').sum) ω =
      (l₁.map fun j => PF.P X (f₁ j) ω).sum + c₃ * PF.P X g₃ ω +
        (l₅.map fun d => PF.P X (f₅ d) ω).sum := by
  have g1 := good_listSum A l₁ h₁
  have g5 := good_listSum A l₅ h₅
  have g3 : A.Good fun ω => c₃ * g₃ ω := A.laws.good_mul _ _ (A.laws.good_const _) h₃
  have g13 : A.Good fun ω => (l₁.map fun q => f₁ q ω).sum + c₃ * g₃ ω :=
    A.laws.good_add _ _ g1 g3
  rw [P_add' A g13 g5, P_add' A g1 g3, P_cmul' A _ h₃, P_listSum' A l₁ h₁, P_listSum' A l₅ h₅]

theorem in_Pexp (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (σ' : Atom k (n + 1) → ι) (hσ' : σ' ∘ liftA 1 = σ)
    (β : ι) (hβ : σ' (newA 0) = β) (ω : Ω) :
    PF.P (σ x) (fun ω' => A.G ω' (σ e₁.x) β * -(A.dh (σ x) β (fun ω'' =>
        Kx (cI x) Γ i₁ σ (D ω'') * rv (D ω'') σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps)) ω')) ω =
      ((Γ.edgeIdx x .minus false).map fun j => PF.P (σ x) (fun ω' =>
          rv (D ω') σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω' (σ e₁.x) β * star (A.G ω' (σ (Γ.comps.getD j e₁).x) β)) *
          star (A.G ω' (σ x) (σ x))) ω).sum +
      (is₂.length : ℂ) * PF.P (σ x) (fun ω' => rv (D ω') σ (Γ.comps.eraseIdx i₁) *
          (A.G ω' (σ e₁.x) β * A.G ω' β (σ x))) ω +
      ((PS_iDs x Γ i₁ e₁).map fun d => PF.P (σ x) (fun ω' => rv (D ω') σ' d) ω).sum := by
  rw [P_congr' (fun ω' => in_KEY A σ hpl hIP hL σ' hσ' β hβ ω')]
  have hE : ∀ (is : List ℕ), A.Test fun ω' => rv (D ω') σ (eraseIdxs is Γ.comps) :=
    fun is => rv_test A σ _ (bas_sub hpl fun c hc => mem_eraseIdxs hc)
  have hR : A.Test fun ω' => rv (D ω') σ (Γ.comps.eraseIdx i₁) :=
    rv_test A σ _ (bas_sub hpl fun c hc => List.mem_of_mem_eraseIdx hc)
  have hFb : ∀ c ∈ eraseIdxs (psteps_iXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  refine P_lin3 A (σ x) _ _ _ _ _ _ (fun j _ => A.test_good _ ?_) (A.test_good _ ?_)
    (fun d hd => A.test_good _ ?_) ω
  · exact test_mul' A (test_mul' A (hE _) (test_mul' A (test_G A _ _)
      (test_star' A (test_G A _ _)))) (test_star' A (test_G A _ _))
  · exact test_mul' A hR (test_mul' A (test_G A _ _) (test_G A _ _))
  · obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have hd'b := ((dTerms_spec A σ' (liftA 1 x) (newA 0) _ (plain_bas_lift hFb 1)).1 d' hd').1
    refine rv_test A σ' _ fun c hc => ?_
    rcases List.mem_append.1 hc with hc | hc
    · rcases List.mem_append.1 hc with hc | hc
      · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
        rw [basB_map]
        exact bas_sub hpl (fun c hc => mem_pickIdxs hc) c' hc'
      · exact (hd'b c hc).1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> rfl

end InDeriv

/-! ## Case (iii): the identity at one labelling, and the value of `multiEIn` -/

section InCore

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ} {x : Atom k n} {Γ : Graph k n}

/-- The identity behind [I, (3.14)] in the form of the graphs of `multiEIn`, at one labelling
`σ` of the atoms of the input graph (`τ α` labels the new atom by `α`). -/
theorem in_core (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (hX : Γ.xdotsAt x (psteps_iXIdx x Γ) = true) (σ : Atom k n → ι)
    (τ : ι → Atom k (n + 1) → ι) (hτ1 : ∀ α, τ α ∘ liftA 1 = σ) (hτ2 : ∀ α, τ α (newA 0) = α)
    (ω : Ω) :
    Γ.coeff.eval (msc A.z) * dv (D ω) σ Γ.comps * rv (D ω) σ Γ.comps =
      ((Γ.edgeIdx x .minus false).map fun j => ∑ α, msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω' (σ e₁.x) α * star (A.G ω' (σ (Γ.comps.getD j e₁).x) α)) *
          star (A.G ω' (σ x) (σ x))) ω).sum +
      ∑ α, msc A.z * Γ.coeff.eval (msc A.z) * (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps * (A.G ω' α α - msc A.z)) ω +
      ∑ α, (is₂.length : ℂ) * msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ (Γ.comps.eraseIdx i₁) *
          (A.G ω' (σ e₁.x) α * A.G ω' α (σ x))) ω +
      ((PS_iDs x Γ i₁ e₁).map fun d => ∑ α, msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') (τ α) d) ω).sum +
      Γ.coeff.eval (msc A.z) * dv (D ω) σ Γ.comps *
        PF.op .Q (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω := by
  set c := Γ.coeff.eval (msc A.z)
  set Det := dv (D ω) σ Γ.comps
  have hFb : ∀ c ∈ eraseIdxs (psteps_iXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  have he₁ := ep_spec x (in_e₁_ep hIP hL)
  by_cases hXY : σ x = σ e₁.x
  · have hx1 : i₁ ∈ psteps_iXIdx x Γ := by
      rw [psteps_iXIdx, hIP]
      simp
    obtain ⟨c', hc', hk, hxy⟩ := xdot_of hX hx1 hL
    rw [ite_eq_right (he₁.2.2 rfl).2] at hxy
    have h0 : Det = 0 := dv_xdot_zero (D ω) σ hc' hk hxy hXY
    simp [h0]
  have hpe : (e₁.isPlainB = true) := hpl e₁ (List.mem_of_getElem? hL)
  have hve : ∀ ω', Comp.val (D ω') σ e₁ = A.G ω' (σ e₁.x) (σ x) := by
    intro ω'
    rw [val_edge A σ hpe he₁.1, (he₁.2.2 rfl).1]
    rfl
  set K : Ω → ℂ := fun ω' => Kx (cI x) Γ i₁ σ (D ω') *
    rv (D ω') σ (eraseIdxs (psteps_iXIdx x Γ) Γ.comps) with hKdef
  have hKt : A.Test K :=
    test_mul' A (test_listProd' A _ fun p hp => kx_test A σ hpl in_hcR i₁ hp)
      (rv_test A σ _ fun c hc => (basB_of_plain (hFb c hc)).1)
  have hR1 : ∀ ω', rv (D ω') σ Γ.comps = A.G ω' (σ e₁.x) (σ x) * K ω' := by
    intro ω'
    rw [in_R1 σ hIP hL, hve]
  have hP : PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω =
      msc A.z * ∑ β, (A.S (σ x) β : ℂ) *
        PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps * (A.G ω' β β - msc A.z)) ω +
      msc A.z * ∑ β, (A.S (σ x) β : ℂ) * PF.P (σ x) (fun ω' => A.G ω' (σ e₁.x) β *
        -(A.dh (σ x) β K ω')) ω := by
    rw [P_congr' hR1, ibp_col A (σ x) (σ e₁.x) hKt ω, ite_eq_right (Ne.symm hXY)]
    have h1 : ∀ β, PF.P (σ x) (fun ω' => (A.G ω' β β - msc A.z) * A.G ω' (σ e₁.x) (σ x) *
        K ω') ω = PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps * (A.G ω' β β - msc A.z)) ω :=
      fun β => by
        rw [P_congr' (g := fun ω' => rv (D ω') σ Γ.comps * (A.G ω' β β - msc A.z))
          fun ω' => by rw [hR1]; ring]
    have h2 : ∀ β, PF.P (σ x) (fun ω' => A.G ω' (σ e₁.x) β * A.dh (σ x) β K ω') ω =
        -PF.P (σ x) (fun ω' => A.G ω' (σ e₁.x) β * -(A.dh (σ x) β K ω')) ω := fun β => by
      rw [← P_neg' A (A.test_good _ (test_mul' A (test_G A _ _)
        (test_neg' A (test_dh' A _ _ hKt))))]
      rw [P_congr' (g := fun ω' => -(A.G ω' (σ e₁.x) β * -(A.dh (σ x) β K ω'))) fun ω' => by
        ring]
    simp only [h1, h2]
    simp only [mul_neg, Finset.sum_neg_distrib]
    ring
  rw [show rv (D ω) σ Γ.comps = PF.op .Q (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω +
    PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω by rw [Q_apply']; ring, hP]
  simp only [hKdef, fun β => in_Pexp A σ hpl hIP hL (τ β) (hτ1 β) β (hτ2 β) ω]
  rw [list_finset_comm, list_finset_comm]
  simp only [List.sum_map_mul_left, ← Finset.sum_add_distrib]
  rw [add_comm _ (c * Det * PF.op .Q (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω), mul_add]
  simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun β _ => ?_
  ring


end InCore


section Conj

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The data record with the deterministic matrices `Θ`, `Σ_o`, `Θ^{(n)}_err`, the ghost factor
and the auxiliary matrices conjugated. -/
def conjD (D₀ : Data ι) : Data ι :=
  { D₀ with
    Theta := D₀.Theta.map star
    Sig := fun o => (D₀.Sig o).map star
    ThetaErr := fun a b => (D₀.ThetaErr a b).map star
    ghost := star D₀.ghost
    aux := fun j => (D₀.aux j).map star }

omit [Fintype ι] [DecidableEq ι] in
theorem conjD_conjD (D₀ : Data ι) : conjD (conjD D₀) = D₀ := by
  rcases D₀ with ⟨m, Gm, S, Sp, Sm, Th, Sig, TE, gh, aux⟩
  simp only [conjD, Matrix.map_map]
  congr <;> simp [Function.comp_def]

omit [DecidableEq ι] in
theorem chain_conjD (D₀ : Data ι) (o : List ℕ) :
    (conjD D₀).chain o = (D₀.chain o).map star := by
  unfold Data.chain
  suffices h : ∀ M : Matrix ι ι ℂ, o.foldl (fun M l => M * (conjD D₀).Sig l * (conjD D₀).Theta)
      (M.map star) = (o.foldl (fun M l => M * D₀.Sig l * D₀.Theta) M).map star by
    exact h D₀.Theta
  induction o with
  | nil => intro M; rfl
  | cons l o ih =>
    intro M
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    change M.map (starRingEnd ℂ) * (D₀.Sig l).map (starRingEnd ℂ) *
      D₀.Theta.map (starRingEnd ℂ) = (M * D₀.Sig l * D₀.Theta).map (starRingEnd ℂ)
    rw [Matrix.map_mul, Matrix.map_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem star_ofReal_mat (S : Matrix ι ι ℝ) (a b : ι) :
    star ((S.map fun r => (r : ℂ)) a b) = (S.map fun r => (r : ℂ)) a b := by
  simp [Matrix.map_apply]

/-- The factor of the conjugate component is the conjugate of the factor under `conjD`, when `S`
is real and `S⁻ = \overline{S⁺}`. -/
theorem val_conj {V : Type*} (D₀ : Data ι) (σ : V → ι) (c : Comp V)
    (hS : ∀ a b, star (D₀.S a b) = D₀.S a b) (hSm : D₀.Sm = D₀.Sp.map star) :
    Comp.val D₀ σ { c with kind := c.kind.conj } = star (Comp.val (conjD D₀) σ c) := by
  rcases c with ⟨κ, x, y, mi, l⟩
  have hfl : ∀ (ch : Charge) (w : ℂ), ch.flip.apply w = star (ch.apply w) := by
    intro ch w
    cases ch <;> simp [Charge.flip, Charge.apply]
  cases κ with
  | G ch => simp only [Comp.val, Kind.conj, hfl]; rfl
  | weight ch => simp only [Comp.val, Kind.conj, hfl]; rfl
  | light ch => simp only [Comp.val, Kind.conj, hfl]; rfl
  | inv ch => simp only [Comp.val, Kind.conj, hfl]; rfl
  | wD ch d => simp only [Comp.val, Kind.conj, hfl]; rfl
  | waved w =>
    cases w
    · simp only [Comp.val, Kind.conj]
      exact (hS _ _).symm
    · simp only [Comp.val, Kind.conj, hSm, Matrix.map_apply]
      rfl
    · simp only [Comp.val, Kind.conj]
      change D₀.Sp _ _ = star (D₀.Sm _ _)
      rw [hSm, Matrix.map_apply, star_star]
  | theta o =>
    simp only [Comp.val, Kind.conj, chain_conjD, Matrix.map_apply, star_star]
  | thetaErr a b => simp [Comp.val, Kind.conj, conjD]
  | ghost => simp [Comp.val, Kind.conj, conjD]
  | aux j r b => simp [Comp.val, Kind.conj, conjD]
  | dot => simp only [Comp.val, Kind.conj]; split_ifs <;> simp
  | xdot => simp only [Comp.val, Kind.conj]; split_ifs <;> simp

theorem CVar_conj_eval (z : ℂ) (v : CVar) :
    CVar.eval z (CVar.conj v) = star (CVar.eval z v) := by
  cases v <;> simp [CVar.conj, CVar.eval, star_inv₀]

theorem Coeff_conj_eval (z : ℂ) (p : Coeff) :
    (Coeff.conj p).eval z = star (p.eval z) := by
  unfold Coeff.conj Coeff.eval
  rw [MvPolynomial.eval_map, MvPolynomial.eval₂_rename, Complex.star_def, MvPolynomial.eval,
    MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  congr 1
  funext v
  simp [CVar_conj_eval]

end Conj

section ConjAdm

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}

/-- The model relations hold for the data records `conjD (D ω)`. -/
def conjAdm (A : ModelAdm Ω ι PF D) : ModelAdm Ω ι PF (fun ω => conjD (D ω)) where
  H := A.H
  z := A.z
  S := A.S
  E := A.E
  Meas := A.Meas
  Good := A.Good
  Test := A.Test
  dh := A.dh
  isHermitian := A.isHermitian
  im_pos := A.im_pos
  isSymm := A.isSymm
  nonneg := A.nonneg
  rowSum := A.rowSum
  data_m := A.data_m
  data_G := A.data_G
  data_minor := A.data_minor
  data_S := A.data_S
  data_Sp := A.data_Sp
  data_Sm := A.data_Sm
  data_Theta := fun ω => by
    have h := congrArg (fun M : Matrix ι ι ℂ => M.map (starRingEnd ℂ)) (A.data_Theta ω)
    simp only [Matrix.map_mul] at h
    have hr : ∀ M : Matrix ι ι ℂ, (∀ a b, star (M a b) = M a b) → M.map (starRingEnd ℂ) = M :=
      fun M hM => by ext a b; exact hM a b
    have h1 : ∀ a b, star ((((‖msc A.z‖ ^ 2 : ℝ) : ℂ) • (D ω).S) a b) =
        (((‖msc A.z‖ ^ 2 : ℝ) : ℂ) • (D ω).S) a b := by
      intro a b
      simp [A.data_S, Matrix.map_apply]
    have h2 : ∀ a b, star ((1 - ((‖msc A.z‖ ^ 2 : ℝ) : ℂ) • (D ω).S) a b) =
        (1 - ((‖msc A.z‖ ^ 2 : ℝ) : ℂ) • (D ω).S) a b := by
      intro a b
      rw [Matrix.sub_apply, star_sub, h1, Matrix.one_apply]
      split_ifs <;> simp
    rw [hr _ h1, hr _ h2] at h
    exact h
  laws := A.laws
  meas_add := A.meas_add
  meas_mul := A.meas_mul
  meas_minor := A.meas_minor
  P_star := A.P_star
  good_star := A.good_star
  good_entry := A.good_entry
  good_inv := A.good_inv
  good_H := A.good_H
  test_good := A.test_good
  test_const := A.test_const
  test_add := A.test_add
  test_mul := A.test_mul
  test_star := A.test_star
  test_entry := A.test_entry
  test_dh := A.test_dh
  dh_add := A.dh_add
  dh_mul := A.dh_mul
  dh_const := A.dh_const
  dh_green := A.dh_green
  dh_conj_green := A.dh_conj_green
  ibp := A.ibp

theorem val_conjD_random {V : Type*} (D₀ : Data ι) (σ : V → ι) (c : Comp V)
    (h : c.kind.isRandom = true) : Comp.val (conjD D₀) σ c = Comp.val D₀ σ c := by
  rcases c with ⟨κ, x, y, mi, l⟩
  cases κ <;> first | rfl | simp [Kind.isRandom] at h

/-- Components without label, or random components without minor that are not `(G_{xx})⁻¹` or
`W_D` weights. -/
def OK {V : Type*} (cs : List (Comp V)) : Prop :=
  ∀ c ∈ cs, c.label = none ∨ (c.kind.isRandom = true ∧ basB c = true)

/-- The term of the conjugate graph is the conjugate of the term under `conjD`. -/
theorem termR_conj (A : ModelAdm Ω ι PF D) {k N : ℕ} (g : Graph k N) (hok : OK g.comps)
    (σ : Atom k N → ι) (ω : Ω) :
    g.conj.termR PF D σ ω = star (g.termR PF (fun ω => conjD (D ω)) σ ω) := by
  have hS : ∀ ω a b, star ((D ω).S a b) = (D ω).S a b := fun ω a b => by
    rw [A.data_S]; exact star_ofReal_mat _ a b
  have hc : ∀ ω (c : Comp (Atom k N)), Comp.val (D ω) σ { c with kind := c.kind.conj } =
      star (Comp.val (conjD (D ω)) σ c) := fun ω c => val_conj _ σ c (hS ω) (A.data_Sm ω)
  have hlab : g.conj.labels = g.labels := by
    unfold Graph.labels Graph.conj
    rw [List.filterMap_map]
    rfl
  have hprod : ∀ (ω : Ω) (p : Comp (Atom k N) → Bool), (((g.comps.map fun c =>
      { c with kind := c.kind.conj }).filter p).map (Comp.val (D ω) σ)).prod =
      star (((g.comps.filter fun c => p { c with kind := c.kind.conj }).map
        (Comp.val (conjD (D ω)) σ)).prod) := by
    intro ω p
    rw [List.filter_map, List.map_map, Complex.star_def, map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun c _ => by
      simp only [Function.comp_apply, hc, Complex.star_def])
  unfold Graph.termR
  rw [hlab]
  simp only [Graph.conj, Coeff_conj_eval] at hprod ⊢
  rw [hprod ω]
  have hop : ∀ ℓ ∈ g.labels, PF.op ℓ.1 (σ ℓ.2) (fun ω' => (((g.comps.map fun c =>
      { c with kind := c.kind.conj }).filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (D ω') σ)).prod) ω =
      star (PF.op ℓ.1 (σ ℓ.2) (fun ω' => ((g.comps.filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (conjD (D ω')) σ)).prod) ω) := by
    intro ℓ hℓ
    have hf : (fun ω' => (((g.comps.map fun c => { c with kind := c.kind.conj }).filter
        fun c => decide (c.label = some ℓ)).map (Comp.val (D ω') σ)).prod) =
        fun ω' => star (((g.comps.filter fun c => decide (c.label = some ℓ)).map
          (Comp.val (conjD (D ω')) σ)).prod) := funext fun ω' => hprod ω' _
    have hgood : A.Good fun ω' => ((g.comps.filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (conjD (D ω')) σ)).prod := by
      refine A.test_good _ (test_listProd' A _ fun c hc' => ?_)
      obtain ⟨hcm, hcl⟩ := List.mem_filter.1 hc'
      rcases hok c hcm with h | ⟨hr, hb⟩
      · simp [h] at hcl
      · simp only [val_conjD_random _ σ c hr]
        exact val_test A σ c hb hr
    rw [hf]
    rcases ℓ with ⟨pq, u⟩
    cases pq
    · exact congrFun (A.P_star _ _ hgood) ω
    · simp only [PFamily.op, Pi.sub_apply, star_sub]
      rw [congrFun (A.P_star _ _ hgood) ω]
  rw [List.map_congr_left hop, Complex.star_def, map_mul, map_mul]
  simp only [map_list_prod, List.map_map, Function.comp_def]
  rfl

theorem valR_conj (A : ModelAdm Ω ι PF D) {k N : ℕ} (g : Graph k N) (hok : OK g.comps)
    (e : Fin k → ι) (ω : Ω) :
    g.conj.valR PF D e ω = star (g.valR PF (fun ω => conjD (D ω)) e ω) := by
  simp only [Graph.valR, termR_conj A g hok, Complex.star_def, map_sum]

end ConjAdm

/-! ## Terms of graphs `Γ_ω P_y(𝒢)` -/

section PTerm

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k N : ℕ}

include A in
theorem P_const' (y : ι) (a : ℂ) (ω : Ω) : PF.P y (fun _ => a) ω = a := by
  have := A.laws.of_meas y (fun _ => a) (A.laws.good_const a) (A.laws.meas_const y a)
  exact congrFun this ω

theorem filter_rl_unl {V : Type*} (y : V) (cs : List (Comp V))
    (h : ∀ c ∈ cs, c.label = none) :
    (cs.map (rl y)).filter (fun c => c.label.isNone) = cs.filter fun c => !c.kind.isRandom := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have ih' := ih fun d hd => h d (List.mem_cons_of_mem _ hd)
    have hc := h c (List.mem_cons_self ..)
    simp only [List.map_cons, List.filter_cons, rl]
    by_cases hr : c.kind.isRandom = true
    · simp [hr, ih']
    · simp [hr, hc, ih']

theorem filter_rl_lab {V : Type*} [DecidableEq V] (y : V) (cs : List (Comp V))
    (h : ∀ c ∈ cs, c.label = none) :
    (cs.map (rl y)).filter (fun c => decide (c.label = some (.P, y))) =
      (cs.filter fun c => c.kind.isRandom).map (rl y) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have ih' := ih fun d hd => h d (List.mem_cons_of_mem _ hd)
    have hc := h c (List.mem_cons_self ..)
    simp only [List.map_cons, List.filter_cons, rl]
    by_cases hr : c.kind.isRandom = true
    · simp [hr, ih', rl]
    · simp [hr, hc, ih']

theorem val_rl {V : Type*} (D₀ : Data ι) (σ : V → ι) (y : V) (c : Comp V) :
    Comp.val D₀ σ (rl y c) = Comp.val D₀ σ c := by
  unfold rl; split_ifs <;> rfl

include A in
/-- The term of a graph whose random components of `cs` carry the label `P_y`, the other
components (of `cs` and of `env`) no label. -/
theorem termR_lifted (y : Atom k N) (cs env : List (Comp (Atom k N))) (co : Coeff)
    (hcs : ∀ c ∈ cs, c.label = none) (henv : ∀ c ∈ env, c.label = none)
    (σ : Atom k N → ι) (ω : Ω) :
    Graph.termR (⟨cs.map (rl y) ++ env, co⟩ : Graph k N) PF D σ ω =
      co.eval (D ω).m * dv (D ω) σ cs * pv (D ω) σ env *
        PF.P (σ y) (fun ω' => rv (D ω') σ cs) ω := by
  have hfe : env.filter (fun c => c.label.isNone) = env :=
    List.filter_eq_self.2 fun c hc => by simp [henv c hc]
  have hfe' : ∀ ℓ : PQ × Atom k N, env.filter (fun c => decide (c.label = some ℓ)) = [] :=
    fun ℓ => List.filter_eq_nil_iff.2 fun c hc => by simp [henv c hc]
  have hunl : (((cs.map (rl y) ++ env).filter fun c => c.label.isNone).map
      (Comp.val (D ω) σ)).prod = dv (D ω) σ cs * pv (D ω) σ env := by
    rw [List.filter_append, filter_rl_unl y cs hcs, hfe, List.map_append, List.prod_append]
    rfl
  by_cases hr : ∃ c ∈ cs, c.kind.isRandom = true
  · have hlab : (Graph.labels (⟨cs.map (rl y) ++ env, co⟩ : Graph k N)) = [(.P, y)] := by
      unfold Graph.labels
      simp only
      apply dedup_eq_singleton
      · intro l hl
        obtain ⟨c, hc, hcl⟩ := List.mem_filterMap.1 hl
        rcases List.mem_append.1 hc with hc | hc
        · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
          unfold rl at hcl
          split_ifs at hcl
          · exact (Option.some.inj hcl).symm
          · rw [hcs d hd] at hcl; cases hcl
        · rw [henv c hc] at hcl; cases hcl
      · obtain ⟨c, hc, hcr⟩ := hr
        exact List.mem_filterMap.2 ⟨rl y c, List.mem_append_left _ (List.mem_map.2 ⟨c, hc, rfl⟩),
          by simp [rl, hcr]⟩
    have hf : (fun ω' => (((cs.map (rl y) ++ env).filter fun c =>
        decide (c.label = some (.P, y))).map (Comp.val (D ω') σ)).prod) =
        fun ω' => rv (D ω') σ cs := by
      funext ω'
      rw [List.filter_append, filter_rl_lab y cs hcs, hfe', List.append_nil, List.map_map]
      unfold rv
      congr 1
      exact List.map_congr_left fun c _ => val_rl _ _ y c
    unfold Graph.termR
    rw [hlab, hunl]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, PFamily.op]
    rw [hf]
    ring
  · push Not at hr
    have hlab : (Graph.labels (⟨cs.map (rl y) ++ env, co⟩ : Graph k N)) = [] := by
      unfold Graph.labels
      rw [List.dedup_eq_nil, List.filterMap_eq_nil_iff]
      intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
        unfold rl
        rw [if_neg (by simp [hr d hd])]
        exact hcs d hd
      · exact henv c hc
    have hrv : ∀ ω', rv (D ω') σ cs = 1 := by
      intro ω'
      unfold rv
      rw [List.filter_eq_nil_iff.2 (fun c hc => by simp [hr c hc])]
      rfl
    unfold Graph.termR
    rw [hlab, hunl]
    simp only [List.map_nil, List.prod_nil, mul_one]
    rw [show (fun ω' => rv (D ω') σ cs) = fun _ => (1 : ℂ) from funext hrv, P_const' A]
    ring

theorem pCore_unl (g : Graph k N) : ∀ c ∈ g.pCore.comps, c.label = none := by
  intro c hc
  rw [pCore_comps] at hc
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 hc
  rfl

theorem pEnv_unl (g : Graph k N) : ∀ c ∈ g.pEnv, c.label = none := by
  intro c hc
  unfold Graph.pEnv at hc
  have := (List.mem_filter.1 hc).2
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at this
  exact this.1

include A in
/-- The term of a graph `Γ_ω P_x(𝒢)`: the coefficient, the deterministic factors of `𝒢` and of
`Γ_ω`, the random factors of `Γ_ω`, and `P_x` of the random factors of `𝒢`. -/
theorem termR_pform {x : Atom k N} {g : Graph k N}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hlr : g.LabRand)
    (σ : Atom k N → ι) (ω : Ω) :
    g.termR PF D σ ω = g.coeff.eval (D ω).m * dv (D ω) σ g.pCore.comps * pv (D ω) σ g.pEnv *
      PF.P (σ x) (fun ω' => rv (D ω') σ g.pCore.comps) ω := by
  have hp : g.comps.Perm (g.pCore.comps.map (rl x) ++ g.pEnv) := by
    rw [relab_pCore hlab hlr]
    exact comps_perm_core g
  rcases g with ⟨L, co⟩
  rw [termR_perm' PF D hp co σ ω]
  exact termR_lifted A x _ _ co (pCore_unl _) (pEnv_unl _) σ ω

end PTerm

/-! ## `O^{(x),1}_weight` inside `P_x` -/

section SplitReg

variable {V : Type*} [DecidableEq V]

/-- A regular weight without label on `x`. -/
def isRegAt (x : V) (c : Comp V) : Bool :=
  (match c.kind with
    | .weight _ => true
    | _ => false) && decide (c.x = x) && c.label.isNone

theorem isRegAt_iff (x : V) (c : Comp V) :
    isRegAt x c = true ↔ (∃ ch, c.kind = .weight ch) ∧ c.x = x ∧ c.label = none := by
  unfold isRegAt
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ <;> simp [Option.isNone_iff_eq_none]

theorem splitRegular_nonreg (x : V) (c : Comp V) (cs : List (Comp V))
    (h : isRegAt x c = false) :
    splitRegular x (c :: cs) = (splitRegular x cs).map fun p => (c :: p.1, p.2) := by
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ with
  | weight ch =>
    simp only [splitRegular]
    by_cases ha : a = x
    · have hl : l ≠ none := fun hl => by simp [isRegAt, ha, hl] at h
      simp [ha, Option.isNone_iff_eq_none, hl]
    · simp [ha]
  | _ => simp [splitRegular]

theorem splitRegular_reg (x : V) (c : Comp V) (cs : List (Comp V)) (h : isRegAt x c = true)
    {ch : Charge} (hk : c.kind = .weight ch) :
    splitRegular x (c :: cs) =
      (splitRegular x cs).map (fun p => (p.1, mOf ch * p.2)) ++
        (splitRegular x cs).map fun p => ({ c with kind := .light ch } :: p.1, p.2) := by
  obtain ⟨-, hx, hl⟩ := (isRegAt_iff x c).1 h
  rcases c with ⟨κ, a, b, mi, l⟩
  simp only at hk hx hl
  subst hk hx hl
  simp [splitRegular]

/-- The light weight with the kind of a regular weight. -/
def toLight (c : Comp V) : Comp V :=
  { c with kind := match c.kind with
    | .weight ch => .light ch
    | κ => κ }

/-- The outputs of `splitRegular`: some regular weights on `x` become light weights, the others are
removed, the other components are kept. -/
theorem splitRegular_dec (x : V) (cs : List (Comp V)) :
    ∀ p ∈ splitRegular x cs, ∃ W₁ W₂ rest : List (Comp V), cs.Perm (W₁ ++ W₂ ++ rest) ∧
      p.1.Perm (W₁.map toLight ++ rest) ∧ (∀ c ∈ W₁ ++ W₂, isRegAt x c = true) ∧
      (∀ c ∈ rest, isRegAt x c = false) := by
  induction cs with
  | nil =>
    intro p hp
    simp only [splitRegular, List.mem_singleton] at hp
    subst hp
    exact ⟨[], [], [], by simp, by simp, by simp, by simp⟩
  | cons c cs ih =>
    intro p hp
    by_cases hr : isRegAt x c = true
    · obtain ⟨⟨ch, hk⟩, -, -⟩ := (isRegAt_iff x c).1 hr
      rw [splitRegular_reg x c cs hr hk] at hp
      rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        obtain ⟨W₁, W₂, rest, h1, h2, h3, h4⟩ := ih q hq
        refine ⟨W₁, c :: W₂, rest, ?_, h2, ?_, h4⟩
        · refine (h1.cons c).trans ?_
          simp only [List.append_assoc, List.cons_append]
          exact (List.perm_middle).symm
        · intro d hd
          simp only [List.mem_append, List.mem_cons] at hd
          rcases hd with hd | rfl | hd
          · exact h3 d (List.mem_append_left _ hd)
          · exact hr
          · exact h3 d (List.mem_append_right _ hd)
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        obtain ⟨W₁, W₂, rest, h1, h2, h3, h4⟩ := ih q hq
        refine ⟨c :: W₁, W₂, rest, ?_, ?_, ?_, h4⟩
        · simpa using h1.cons c
        · have : toLight c = { c with kind := .light ch } := by simp [toLight, hk]
          simpa [this] using h2.cons (toLight c)
        · intro d hd
          simp only [List.mem_append, List.mem_cons] at hd
          rcases hd with (rfl | hd) | hd
          · exact hr
          · exact h3 d (List.mem_append_left _ hd)
          · exact h3 d (List.mem_append_right _ hd)
    · have hr' : isRegAt x c = false := by simpa using hr
      rw [splitRegular_nonreg x c cs hr'] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      obtain ⟨W₁, W₂, rest, h1, h2, h3, h4⟩ := ih q hq
      refine ⟨W₁, W₂, c :: rest, ?_, ?_, h3, ?_⟩
      · exact (h1.cons c).trans List.perm_middle.symm
      · exact (h2.cons c).trans List.perm_middle.symm
      · intro d hd
        rcases List.mem_cons.1 hd with rfl | hd
        · exact hr'
        · exact h4 d hd

end SplitReg

section SplitRegValue

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type*} [DecidableEq V]

/-- The values of the outputs of `splitRegular`: the random parts sum to the random part of the
input, the deterministic parts are those of the input. -/
theorem splitRegular_value (x : V) (cs : List (Comp V)) (D₀ : Data ι) (σ : V → ι) :
    ((splitRegular x cs).map fun p => p.2.eval D₀.m * rv D₀ σ p.1).sum = rv D₀ σ cs ∧
      ∀ p ∈ splitRegular x cs, dv D₀ σ p.1 = dv D₀ σ cs := by
  induction cs with
  | nil => simp [splitRegular, Coeff.eval]
  | cons c cs ih =>
    obtain ⟨ih1, ih2⟩ := ih
    by_cases hr : isRegAt x c = true
    · obtain ⟨⟨ch, hk⟩, -, -⟩ := (isRegAt_iff x c).1 hr
      rw [splitRegular_reg x c cs hr hk]
      have hrc : c.kind.isRandom = true := by rw [hk]; rfl
      refine ⟨?_, ?_⟩
      · simp only [List.map_append, List.map_map, Function.comp_def, List.sum_append, rv_cons,
          hrc, ite_true, Kind.isRandom, ↓reduceIte]
        have e1 : ∀ p : List (Comp V) × Coeff, (mOf ch * p.2).eval D₀.m * rv D₀ σ p.1 =
            (mOf ch).eval D₀.m * (p.2.eval D₀.m * rv D₀ σ p.1) := by
          intro p; simp only [Coeff.eval, map_mul]; ring
        have e2 : ∀ p : List (Comp V) × Coeff, p.2.eval D₀.m * (Comp.val D₀ σ
            { c with kind := .light ch } * rv D₀ σ p.1) =
            Comp.val D₀ σ { c with kind := .light ch } * (p.2.eval D₀.m * rv D₀ σ p.1) := by
          intro p; ring
        simp only [e1, e2, List.sum_map_mul_left, ih1]
        rw [← add_mul]
        congr 1
        rcases c with ⟨κ, a, b, mi, l⟩
        simp only at hk
        subst hk
        cases ch <;> simp [Comp.val, mOf, Coeff.eval, CVar.eval, Charge.apply]
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          rw [ih2 q hq, dv_cons, if_pos hrc, one_mul]
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          rw [dv_cons, dv_cons, ih2 q hq, if_pos hrc,
            if_pos (show ({ c with kind := .light ch } : Comp V).kind.isRandom = true from rfl)]
    · have hr' : isRegAt x c = false := by simpa using hr
      rw [splitRegular_nonreg x c cs hr']
      refine ⟨?_, ?_⟩
      · simp only [List.map_map, Function.comp_def, rv_cons]
        have e : ∀ p : List (Comp V) × Coeff, p.2.eval D₀.m *
            ((if c.kind.isRandom then Comp.val D₀ σ c else 1) * rv D₀ σ p.1) =
            (if c.kind.isRandom then Comp.val D₀ σ c else 1) * (p.2.eval D₀.m * rv D₀ σ p.1) := by
          intro p; ring
        simp only [e, List.sum_map_mul_left, ih1]
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        rw [dv_cons, dv_cons, ih2 q hq]

end SplitRegValue

/-! ## The clauses on the terms of one step inside `P_x` -/

section TermOKDef

variable {k n : ℕ}

/-- The clauses on a term `t` of one step inside `P_x` applied to `g` at `x`, before the
normalization: the clauses `NN` with bound `C₁`, at most three solid edges without `×`-dotted
edge, at most two between two blocks, the clauses `SR`, the scaling order does not drop, and if
it is unchanged the weighted number of labelled weights and edge ends at the block of `x` drops
and the normalization makes no identification of the same scaling order. -/
structure PStepsTermOK (C₁ : ℕ) (x : Atom k n) (g : Graph k n) (t : Tracked k n) : Prop where
  nn : NN C₁ (t.f x) t.g
  unp : t.g.unpart.length ≤ 3
  bnd : t.g.unpart.length + t.g.orph.length ≤ C₁
  beta : t.g.Beta 2
  sr : SR g x t
  ord : g.ord ≤ t.g.ord
  eq : t.g.ord = g.ord → t.g.pw (t.f x) < g.pw x ∧ (t.g.Beta 1 ∨ t.g.HAvoid (t.f x))

theorem Graph.beta_of_unpart {g : Graph k n} {b : ℕ} (h : g.unpart.length ≤ b) :
    g.Beta b := by
  intro u v _
  classical
  unfold Graph.nBetween
  exact (List.length_filter_le _ _).trans h

end TermOKDef

/-! ## `O^{(x),1}_weight` inside `P_x`: the terms -/

section WeightSwap

variable {k n : ℕ}

/-- A weight or light weight with label `P_x` on `x`. -/
def WtAt (x : Atom k n) (c : Comp (Atom k n)) : Prop :=
  ((∃ ch, c.kind = .weight ch) ∨ (∃ ch, c.kind = .light ch)) ∧ c.x = x ∧ c.y = x ∧
    c.minor = [] ∧ c.label = some (.P, x)

/-- Replacing labelled weights on `x` by other labelled weights on `x` keeps the clauses. -/
theorem weightSwap {C : ℕ} {x : Atom k n} {g g₁ : Graph k n} (hS : St C x g)
    {R A L : List (Comp (Atom k n))} (hR : g.comps.Perm (R ++ L)) (h₁ : g₁.comps.Perm (A ++ L))
    (hRw : ∀ c ∈ R, WtAt x c) (hAw : ∀ c ∈ A, WtAt x c) (hlen : A.length ≤ R.length)
    (hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n, g₁⟩) :
    St C x g₁ ∧ SR g x (Tracked.self g₁) ∧
      g₁.ord = g.ord - psteps_ordL R + psteps_ordL A ∧
      g₁.pw x + (R.map (wBP fun u => g.SameBlock u x)).sum =
        g.pw x + (A.map (wBP fun u => g.SameBlock u x)).sum := by
  have hN := hS.nn
  have hnw : ∀ c, WtAt x c → c.kind ≠ .dot ∧ c.kind ≠ .xdot ∧ c.kind.isSolid = false ∧
      c.kind.isRandom = true := by
    rintro c ⟨⟨ch, hk⟩ | ⟨ch, hk⟩, -⟩ <;> rw [hk] <;> simp [Kind.isSolid, Kind.isRandom]
  have hmemg : ∀ c, c ∈ g.comps ↔ c ∈ R ∨ c ∈ L := fun c => by rw [hR.mem_iff, List.mem_append]
  have hmem₁ : ∀ c, c ∈ g₁.comps ↔ c ∈ A ∨ c ∈ L := fun c => by rw [h₁.mem_iff, List.mem_append]
  -- the components that are not weights of `R` or `A` are the same
  have hsame : ∀ c, ¬ WtAt x c → (c ∈ g₁.comps ↔ c ∈ g.comps) := by
    intro c hc
    rw [hmem₁, hmemg]
    constructor
    · rintro (h | h)
      · exact absurd (hAw c h) hc
      · exact Or.inr h
    · rintro (h | h)
      · exact absurd (hRw c h) hc
      · exact Or.inr h
  have hdx : ∀ c, (c.kind = .dot ∨ c.kind = .xdot ∨ c.kind.isSolid = true) →
      (c ∈ g₁.comps ↔ c ∈ g.comps) := by
    intro c hc
    refine hsame c fun hw => ?_
    obtain ⟨h1, h2, h3, -⟩ := hnw c hw
    rcases hc with h | h | h
    · exact h1 h
    · exact h2 h
    · rw [h3] at h; cases h
  have hbl : ∀ u v, g₁.SameBlock u v ↔ g.SameBlock u v :=
    Graph.sameBlock_iff_of_dots fun c hk => (hdx c (Or.inl hk)).symm |>.symm
  have hpartB : ∀ c, g₁.partB c = g.partB c := by
    intro c
    rw [Bool.eq_iff_iff, Graph.partB_iff, Graph.partB_iff]
    constructor
    · rintro ⟨d, hd, hk, hp⟩; exact ⟨d, (hdx d (Or.inr (Or.inl hk))).1 hd, hk, hp⟩
    · rintro ⟨d, hd, hk, hp⟩; exact ⟨d, (hdx d (Or.inr (Or.inl hk))).2 hd, hk, hp⟩
  have hsolidB : ∀ c, g₁.solidB c = g.solidB c := by
    intro c
    rw [Bool.eq_iff_iff, Graph.solidB_iff, Graph.solidB_iff]
    constructor
    · rintro ⟨d, hd, hk, hp⟩; exact ⟨d, (hdx d (Or.inr (Or.inr hk))).1 hd, hk, hp⟩
    · rintro ⟨d, hd, hk, hp⟩; exact ⟨d, (hdx d (Or.inr (Or.inr hk))).2 hd, hk, hp⟩
  have hunp : g₁.unpart = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro c hc
    obtain ⟨hcm, hcs, hcp⟩ := Graph.mem_unpart.1 hc
    have : c ∈ g.unpart := Graph.mem_unpart.2 ⟨(hdx c (Or.inr (Or.inr hcs))).1 hcm, hcs,
      by rw [← hpartB]; exact hcp⟩
    rw [hS.unp] at this; simp at this
  have horph : g₁.orph = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro c hc
    obtain ⟨hcm, hck, hcs⟩ := Graph.mem_orph.1 hc
    have : c ∈ g.orph := Graph.mem_orph.2 ⟨(hdx c (Or.inr (Or.inl (by simpa using hck)))).1 hcm,
      hck, by rw [← hsolidB]; exact hcs⟩
    rw [hS.orp] at this; simp at this
  -- the edge graphs are the same: weights are loops
  have hedge : ∀ c ∈ g₁.comps, c ∉ g.comps → c.x = c.y := by
    intro c hc hc'
    by_cases hw : WtAt x c
    · rw [hw.2.1, hw.2.2.1]
    · exact absurd ((hsame c hw).1 hc) hc'
  have hedge' : ∀ c ∈ g.comps, c ∉ g₁.comps → c.x = c.y := by
    intro c hc hc'
    by_cases hw : WtAt x c
    · rw [hw.2.1, hw.2.2.1]
    · exact absurd ((hsame c hw).2 hc) hc'
  have hcnx : g₁.ConnNoX := by
    intro a b
    refine SimpleGraph.Reachable.mono ?_ (hN.cnx a b)
    intro p q hpq
    rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj] at hpq ⊢
    rcases hpq with ⟨hne, ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩⟩
    · by_cases hc₁ : c ∈ g₁.comps
      · exact ⟨hne, Or.inl ⟨c, hc₁, hk, h1, h2⟩⟩
      · exact absurd (by rw [← h1, ← h2]; exact hedge' c hc hc₁) hne
    · by_cases hc₁ : c ∈ g₁.comps
      · exact ⟨hne, Or.inr ⟨c, hc₁, hk, h1, h2⟩⟩
      · exact absurd (by rw [← h1, ← h2]; exact (hedge' c hc hc₁).symm) hne
  have hint : ∀ a b : Fin n, g₁.wavedThetaGraph.Reachable (.inr a) (.inr b) := by
    intro a b
    refine SimpleGraph.Reachable.mono ?_ (hN.reg.internal a b)
    intro p q hpq
    rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at hpq ⊢
    rcases hpq with ⟨hne, ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩⟩
    · by_cases hc₁ : c ∈ g₁.comps
      · exact ⟨hne, Or.inl ⟨c, hc₁, hk, h1, h2⟩⟩
      · exact absurd (by rw [← h1, ← h2]; exact hedge' c hc hc₁) hne
    · by_cases hc₁ : c ∈ g₁.comps
      · exact ⟨hne, Or.inr ⟨c, hc₁, hk, h1, h2⟩⟩
      · exact absurd (by rw [← h1, ← h2]; exact (hedge' c hc hc₁).symm) hne
  have hsize : g₁.comps.length ≤ g.comps.length := by
    have := h₁.length_eq; have := hR.length_eq
    simp only [List.length_append] at *; omega
  have hNN : NN C x g₁ := by
    refine ⟨hN.hx, ⟨by have := hN.reg.size; omega, ConnNoX.connected hcnx, hint, ?_⟩, hcnx, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc hk; exact hN.reg.noIntDot c ((hdx c (Or.inl hk)).1 hc) hk
    · intro c hc hk; exact hN.noLoop c ((hdx c (Or.inr (Or.inr hk))).1 hc) hk
    · intro c hc
      by_cases hw : WtAt x c
      · obtain ⟨hk, hx, hy, hmi, hl⟩ := hw
        refine ⟨hmi, ?_, ?_, ?_, ?_, ?_⟩
        · intro ch h; rcases hk with ⟨ch', hk⟩ | ⟨ch', hk⟩ <;> rw [hk] at h <;> cases h
        · intro ch d h; rcases hk with ⟨ch', hk⟩ | ⟨ch', hk⟩ <;> rw [hk] at h <;> cases h
        · intro h; rcases hk with ⟨ch', hk⟩ | ⟨ch', hk⟩ <;> rw [hk] at h <;> cases h
        · intro _; rw [hx, hy]
        · intro _; rcases hk with ⟨ch', hk⟩ | ⟨ch', hk⟩ <;> rw [hk] <;> rfl
      · exact hN.plain c ((hsame c hw).1 hc)
    · intro c hc
      by_cases hw : WtAt x c
      · exact Or.inr hw.2.2.2.2
      · exact hN.lab c ((hsame c hw).1 hc)
    · intro c hc hk; rw [hbl]; exact hN.xa c ((hdx c (Or.inr (Or.inl hk))).1 hc) hk
    · intro a b h; exact hN.ib a b ((hbl _ _).1 h)
    · intro c hc hk; rw [hbl]; exact hN.inBlk c ((hdx c (Or.inr (Or.inr hk))).1 hc) hk
    · intro c hc; rw [hunp] at hc; simp at hc
    · intro c hc; rw [hunp] at hc; simp at hc
  have hS6 : g₁.S6 x := by
    intro c hc hl
    rw [hbl, hbl]
    by_cases hw : WtAt x c
    · exact ⟨fun _ => hw.2.1, fun _ => hw.2.2.1⟩
    · exact hS.s6 c ((hsame c hw).1 hc) hl
  have hexc : excL g₁.comps = excL g.comps := by
    rw [excL_perm h₁, excL_perm hR, excL_append_nodot L A (fun c hc => (hnw c (hAw c hc)).1),
      excL_append_nodot L R (fun c hc => (hnw c (hRw c hc)).1)]
  refine ⟨⟨hNN, hunp, horph, hS6⟩, ?_, ?_, ?_⟩
  · refine SR.of_id hN.hx hN.plain.labRand ?_ (fun c hc hk => (hdx c (Or.inl hk)).2 hc) ?_
      (le_of_eq hexc) hch
    · have h1 := hR.filter (fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot))
      have h2 := h₁.filter (fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot))
      rw [List.filter_append, (List.filter_eq_nil_iff (l := R)).2 (fun c hc => by
        simp [(hRw c hc).2.2.2.2]), List.nil_append] at h1
      rw [List.filter_append, (List.filter_eq_nil_iff (l := A)).2 (fun c hc => by
        simp [(hAw c hc).2.2.2.2]), List.nil_append] at h2
      exact (h1.trans h2.symm).subperm.trans List.filter_sublist.subperm
    · intro c hc hk _ _; exact (hdx c (Or.inr (Or.inr (by rw [hk]; rfl)))).2 hc
  · unfold Graph.ord psteps_ordL
    rw [(h₁.map _).sum_eq, (hR.map _).sum_eq]
    simp only [List.map_append, List.sum_append]
    ring
  · unfold Graph.pw
    rw [blockPred_congr x hbl, (h₁.map _).sum_eq, (hR.map _).sum_eq]
    simp only [List.map_append, List.sum_append]
    ring

end WeightSwap

section RoundW

variable {k n : ℕ}

theorem map_comp_id {V : Type*} (L : List (Comp V)) : L.map (Comp.map id) = L := by
  conv_rhs => rw [← List.map_id L]
  refine List.map_congr_left fun c _ => ?_
  rcases c with ⟨κ, a, b, mi, l⟩
  rcases l with _ | ⟨pq, u⟩ <;> simp [Comp.map]

theorem pLiftT_oWeight1T (x : Atom k n) (g : Graph k n) :
    pLiftT x g (oWeight1T x g.pCore) = (splitRegular x g.pCore.comps).map fun p =>
      (⟨n, ⟨p.1.map (rl x) ++ g.pEnv, p.2 * g.coeff⟩, id⟩ : Tracked k n) := by
  unfold pLiftT oWeight1T
  rw [List.filterMap_map]
  apply List.filterMap_eq_map_iff_forall_eq_some.2
  intro p hp
  have hunl : ∀ c ∈ p.1, c.label = none := by
    intro c hc
    obtain ⟨W₁, W₂, rest, h1, h2, -, -⟩ := splitRegular_dec x _ p hp
    rcases List.mem_append.1 (h2.subset hc) with h | h
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
      exact pCore_unl g w (h1.symm.subset (by simp [hw]))
    · exact pCore_unl g c (h1.symm.subset (by simp [h]))
  have hq : ¬ (p.1.any fun c => decide (c.label = some (.Q, id x))) = true := by
    simp only [List.any_eq_true, decide_eq_true_eq, not_exists, not_and]
    intro c hc
    rw [hunl c hc]
    simp
  simp only [Function.comp_apply]
  rw [if_neg hq, map_comp_id]
  rfl

theorem pCore_mem {g : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ g.pCore.comps) :
    ∃ d ∈ g.comps, coreP d = true ∧ c = { d with label := none } := by
  rw [pCore_comps] at hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  exact ⟨d, (List.mem_filter.1 hd).1, (List.mem_filter.1 hd).2, rfl⟩

theorem pCore_random {g : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ g.pCore.comps)
    (hr : c.kind.isRandom = true) : ∃ d ∈ g.comps, d.label.isSome = true ∧
      c = { d with label := none } := by
  obtain ⟨d, hd, hcp, rfl⟩ := pCore_mem hc
  refine ⟨d, hd, ?_, rfl⟩
  unfold coreP at hcp
  simp only at hr
  simpa [hr] using hcp

/-- The terms of `O^{(x),1}_weight` inside `P_x`. -/
theorem termsW {S : ℕ} {x : Atom k n} {g : Graph k n} (hS : St S x g)
    (hW : ∃ c ∈ g.pCore.comps, isRegAt x c = true) :
    ∀ t ∈ pLiftT x g (oWeight1T x g.pCore), PStepsTermOK S x g t ∧ t.g.comps.length ≤ g.comps.length ∧
      t.nOut = n := by
  have hN := hS.nn
  intro t ht
  rw [pLiftT_oWeight1T] at ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  obtain ⟨W₁, W₂, rest, h1, h2, h3, h4⟩ := splitRegular_dec x _ p hp
  set R := (W₁ ++ W₂).map (rl x)
  set A := (W₁.map toLight).map (rl x)
  set L := rest.map (rl x) ++ g.pEnv
  have hgR : g.comps.Perm (R ++ L) := by
    have hp0 : g.comps.Perm (g.pCore.comps.map (rl x) ++ g.pEnv) := by
      rw [relab_pCore hN.lab hN.plain.labRand]; exact comps_perm_core g
    refine hp0.trans ?_
    have := (h1.map (rl x)).append_right g.pEnv
    simpa [R, L, List.append_assoc] using this
  have hgA : (p.1.map (rl x) ++ g.pEnv).Perm (A ++ L) := by
    have := (h2.map (rl x)).append_right g.pEnv
    simpa [A, L, List.append_assoc] using this
  -- the weights of `W₁ ++ W₂` are labelled weights on `x`
  have hW' : ∀ w ∈ W₁ ++ W₂, (∃ ch, w.kind = .weight ch) ∧ w.x = x ∧ w.y = x ∧ w.minor = [] := by
    intro w hw
    obtain ⟨⟨ch, hk⟩, hx, -⟩ := (isRegAt_iff x w).1 (h3 w hw)
    obtain ⟨d, hd, -, rfl⟩ := pCore_mem (h1.symm.subset (List.mem_append_left _ hw))
    obtain ⟨hmi, -, -, -, hwf, -⟩ := hN.plain d hd
    have hy : d.y = d.x := hwf (by simp only at hk; rw [hk]; rfl)
    exact ⟨⟨ch, hk⟩, hx, by simp only at hx ⊢; rw [hy]; exact hx, hmi⟩
  have hRw : ∀ c ∈ R, WtAt x c := by
    intro c hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
    obtain ⟨⟨ch, hk⟩, hx, hy, hmi⟩ := hW' w hw
    refine ⟨Or.inl ⟨ch, by simp [rl, hk, Kind.isRandom]⟩, by simp [rl, hk, Kind.isRandom, hx],
      by simp [rl, hk, Kind.isRandom, hy], by simp [rl, hk, Kind.isRandom, hmi],
      by simp [rl, hk, Kind.isRandom]⟩
  have hAw : ∀ c ∈ A, WtAt x c := by
    intro c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc'
    obtain ⟨⟨ch, hk⟩, hx, hy, hmi⟩ := hW' w (List.mem_append_left _ hw)
    refine ⟨Or.inr ⟨ch, by simp [rl, toLight, hk, Kind.isRandom]⟩,
      by simp [rl, toLight, hk, Kind.isRandom, hx], by simp [rl, toLight, hk, Kind.isRandom, hy],
      by simp [rl, toLight, hk, Kind.isRandom, hmi], by simp [rl, toLight, hk, Kind.isRandom]⟩
  have hP : g.IsPFormAt x := by
    obtain ⟨c, hc, hcr⟩ := hW
    obtain ⟨⟨ch, hk⟩, -, -⟩ := (isRegAt_iff x c).1 hcr
    obtain ⟨d, hd, hdl, rfl⟩ := pCore_random hc (by rw [hk]; rfl)
    refine ⟨⟨d, hd, ?_⟩, hN.lab⟩
    rcases hN.lab d hd with h | h
    · rw [h] at hdl; cases hdl
    · exact h
  have hch : Relation.ReflTransGen QElemStep ⟨n, g⟩
      ⟨n, ⟨p.1.map (rl x) ++ g.pEnv, p.2 * g.coeff⟩⟩ := by
    refine .single (QElemStep.pWeight1 x g ⟨n, ⟨p.1.map (rl x) ++ g.pEnv, p.2 * g.coeff⟩, id⟩ hP
      hN.plain ?_)
    rw [pLiftT_oWeight1T]
    exact List.mem_map.2 ⟨p, hp, rfl⟩
  have hlen : A.length ≤ R.length := by simp [A, R]
  obtain ⟨hS₁, hSR, hord, hpw⟩ := weightSwap hS hgR hgA hRw hAw hlen hch
  -- the counts
  have hordR : psteps_ordL R = 0 := by
    unfold psteps_ordL
    rw [List.sum_eq_zero]
    intro z hz
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hz
    obtain ⟨⟨ch, hk⟩ | ⟨ch, hk⟩, -⟩ := hRw c hc
    · rw [hk]; rfl
    · exfalso
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
      obtain ⟨⟨ch', hk'⟩, -⟩ := hW' w hw
      simp [rl, hk', Kind.isRandom] at hk
  have hordA : psteps_ordL A = W₁.length := by
    unfold psteps_ordL
    simp only [A, List.map_map]
    rw [show (W₁.map ((fun c => c.kind.ord) ∘ rl x ∘ toLight)) = W₁.map fun _ => (1 : ℤ) from ?_]
    · simp
    · refine List.map_congr_left fun w hw => ?_
      obtain ⟨⟨ch, hk⟩, -⟩ := hW' w (List.mem_append_left _ hw)
      simp [rl, toLight, hk, Kind.isRandom, Kind.ord]
  have hpwR : (R.map (wBP fun u => g.SameBlock u x)).sum = R.length := by
    rw [show R.map (wBP fun u => g.SameBlock u x) = R.map fun _ => 1 from
      List.map_congr_left fun c hc => ?_]
    · simp
    · obtain ⟨⟨ch, hk⟩ | ⟨ch, hk⟩, hx, -, -, hl⟩ := hRw c hc
      · simp [wBP, hk, hl, hx, Graph.sameBlock_refl]
      · exfalso
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
        obtain ⟨⟨ch', hk'⟩, -⟩ := hW' w hw
        simp [rl, hk', Kind.isRandom] at hk
  have hpwA : (A.map (wBP fun u => g.SameBlock u x)).sum = 4 * A.length := by
    rw [show A.map (wBP fun u => g.SameBlock u x) = A.map fun _ => 4 from
      List.map_congr_left fun c hc => ?_]
    · simp [mul_comm]
    · obtain ⟨⟨ch, hk⟩ | ⟨ch, hk⟩, hx, -, -, hl⟩ := hAw c hc
      · exfalso
        obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc'
        obtain ⟨⟨ch', hk'⟩, -⟩ := hW' w (List.mem_append_left _ hw)
        simp [rl, toLight, hk', Kind.isRandom] at hk
      · simp [wBP, hk, hl, hx, Graph.sameBlock_refl]
  have hRpos : 1 ≤ R.length := by
    obtain ⟨c, hc, hcr⟩ := hW
    have : c ∈ W₁ ++ W₂ := by
      rcases List.mem_append.1 (h1.subset hc) with h | h
      · exact h
      · rw [h4 c h] at hcr; cases hcr
    simp only [R, List.length_map]
    exact List.length_pos_of_mem this
  refine ⟨⟨hS₁.nn, by rw [hS₁.unp]; simp, by rw [hS₁.unp, hS₁.orp]; simp,
    Graph.beta_of_unpart (by rw [hS₁.unp]; simp), hSR, ?_, ?_⟩, ?_, rfl⟩
  · simp only
    rw [hord, hordR, hordA]; push_cast; linarith [Nat.cast_nonneg (α := ℤ) W₁.length]
  · intro heq
    simp only at heq ⊢
    rw [hord, hordR, hordA] at heq
    have hW1 : W₁.length = 0 := by omega
    have hA0 : A.length = 0 := by simp [A, hW1]
    refine ⟨?_, Or.inl (Graph.beta_of_unpart (by rw [hS₁.unp]; simp))⟩
    rw [hpwR, hpwA, hA0] at hpw
    show (⟨p.1.map (rl x) ++ g.pEnv, p.2 * g.coeff⟩ : Graph k n).pw x < g.pw x
    omega
  · simp only
    have := hgA.length_eq
    have := hgR.length_eq
    simp only [List.length_append] at *
    have : A.length ≤ R.length := hlen
    omega

theorem pCore_basB {g : Graph k n} (hp : g.Plain) : ∀ c ∈ g.pCore.comps, basB c = true := by
  intro c hc
  obtain ⟨d, hd, -, rfl⟩ := pCore_mem hc
  obtain ⟨h1, h2, h3, -⟩ := hp d hd
  have hb : basB d = true := by
    unfold basB
    rw [h1]
    cases hk : d.kind with
    | inv ch => exact absurd hk (h2 ch)
    | wD ch dd => exact absurd hk (h3 ch dd)
    | _ => rfl
  exact hb

/-- The value of `O^{(x),1}_weight` inside `P_x`. -/
theorem valueW {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hp : g.Plain) :
    TExpansion.ValueEq (pLiftT x g (oWeight1T x g.pCore)) g modelAdm := by
  intro Ω ι _ _ PF D hA e
  obtain ⟨A⟩ := hA
  funext ω
  rw [pLiftT_oWeight1T]
  simp only [TExpansion.forget, Expansion.valR, List.map_map, Function.comp_def, Graph.valR]
  have hunl : ∀ p ∈ splitRegular x g.pCore.comps, ∀ c ∈ p.1, c.label = none := by
    intro p hp' c hc
    obtain ⟨W₁, W₂, rest, h1, h2, -, -⟩ := splitRegular_dec x _ p hp'
    rcases List.mem_append.1 (h2.subset hc) with h | h
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
      exact pCore_unl g w (h1.symm.subset (by simp [hw]))
    · exact pCore_unl g c (h1.symm.subset (by simp [h]))
  have hterm : ∀ p ∈ splitRegular x g.pCore.comps, ∀ s : Fin n → ι,
      Graph.termR (⟨p.1.map (rl x) ++ g.pEnv, p.2 * g.coeff⟩ : Graph k n) PF D (Sum.elim e s) ω =
        (p.2 * g.coeff).eval (D ω).m * dv (D ω) (Sum.elim e s) p.1 *
          pv (D ω) (Sum.elim e s) g.pEnv *
          PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) p.1) ω :=
    fun p hp' s => termR_lifted A x _ _ _ (hunl p hp') (pEnv_unl g) _ ω
  rw [List.map_congr_left fun p hp' => Finset.sum_congr rfl fun s _ => hterm p hp' s,
    list_finset_comm (splitRegular x g.pCore.comps) (fun p s =>
      (p.2 * g.coeff).eval (D ω).m * dv (D ω) (Sum.elim e s) p.1 *
        pv (D ω) (Sum.elim e s) g.pEnv *
        PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) p.1) ω)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [termR_pform A hlab hp.labRand]
  set σ := Sum.elim e s
  have hv := fun D₀ => splitRegular_value x g.pCore.comps D₀ σ
  have hm : ∀ ω', (D ω').m = msc A.z := A.data_m
  have hbas := pCore_basB hp
  have hsum : (fun ω' => rv (D ω') σ g.pCore.comps) = fun ω' =>
      ((splitRegular x g.pCore.comps).map fun p => p.2.eval (msc A.z) * rv (D ω') σ p.1).sum := by
    funext ω'
    rw [← (hv (D ω')).1, hm]
  have hgood : ∀ p ∈ splitRegular x g.pCore.comps, A.Good fun ω' => rv (D ω') σ p.1 := by
    intro p hp'
    refine A.test_good _ (rv_test A σ _ fun c hc => ?_)
    obtain ⟨W₁, W₂, rest, h1, h2, -, -⟩ := splitRegular_dec x _ p hp'
    rcases List.mem_append.1 (h2.subset hc) with h | h
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
      have := hbas w (h1.symm.subset (by simp [hw]))
      simp only [basB, toLight] at this ⊢
      rcases hk : w.kind <;> simp_all
    · exact hbas c (h1.symm.subset (by simp [h]))
  rw [hsum, P_listSum' A _ (f := fun p ω' => p.2.eval (msc A.z) * rv (D ω') σ p.1)
    (fun p hp' => A.laws.good_mul (fun _ => p.2.eval (msc A.z)) _
      (A.laws.good_const _) (hgood p hp'))]
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun p hp' => ?_)
  rw [(hv (D ω)).2 p hp', P_cmul' A _ (hgood p hp'), hm]
  simp only [Coeff.eval, map_mul]
  ring

end RoundW

/-! ## Solid edges between blocks in a graph with one new atom -/

section ShapeBeta

variable {k n : ℕ}

/-- `a` has the new atom as an end. -/
def touchN (a : Comp (Atom k (n + 1))) : Bool := a.x == newA 0 || a.y == newA 0

/-- The end of `a` other than the new atom. -/
def otherN (a : Comp (Atom k (n + 1))) : Atom k (n + 1) :=
  if a.x = newA 0 then a.y else a.x

theorem Graph.LabIn.congr_right {g : Graph k n} {a b b' : Atom k n} (h : g.LabIn a b)
    (hb : g.SameBlock b b') : g.LabIn a b' := by
  intro c hc hl hca
  obtain ⟨hs, h1 | h1⟩ := h c hc hl hca
  · exact ⟨hs, Or.inl ⟨h1.1, Graph.sameBlock_trans h1.2 hb⟩⟩
  · exact ⟨hs, Or.inr ⟨Graph.sameBlock_trans h1.1 hb, h1.2⟩⟩

theorem length_filter_le_one_of_pairwise {α : Type*} {R : α → α → Prop} {L : List α}
    (hL : L.Pairwise R) (p : α → Bool) (hp : ∀ a b, p a = true → p b = true → ¬ R a b) :
    (L.filter p).length ≤ 1 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha, List.length_cons]
      have : L.filter p = [] :=
        List.filter_eq_nil_iff.2 fun b hb hpb => hp a b ha hpb (hL.1 b hb)
      rw [this]; simp
    · rw [List.filter_cons_of_neg ha]; exact ih hL.2

open Classical in
theorem Graph.nBetween_comm (g : Graph k n) (u v : Atom k n) :
    g.nBetween u v = g.nBetween v u := by
  unfold Graph.nBetween
  congr 1
  apply List.filter_congr
  intro c _
  simp only [decide_eq_decide]
  exact Or.comm

open Classical in
/-- In a graph with one new atom whose solid edges without `×`-dotted edge are among `A`: at most
two of them between two blocks, at most one if the edges at the new atom go to distinct blocks,
and the clause `Graph.HAvoid`. -/
theorem shapeBeta {g₁ : Graph k (n + 1)} {A : List (Comp (Atom k (n + 1)))}
    (hsub : g₁.unpart.Subperm A)
    (hnew : ∀ b, g₁.SameBlock (newA 0) b ↔ b = newA 0)
    (hAb : ∀ a ∈ A, a.kind.isSolid = true → a.x ≠ a.y)
    (hN : (A.filter fun a => a.kind.isSolid && !touchN a).length ≤ 1)
    (hT : (A.filter fun a => a.kind.isSolid && touchN a).length ≤ 2) :
    g₁.Beta 2 ∧
    (((A.filter fun a => a.kind.isSolid && touchN a).map otherN).Pairwise
      (fun a b => ¬ g₁.SameBlock a b) → g₁.Beta 1) ∧
    ∀ y, ¬ g₁.SameBlock (newA 0) y →
      ((∀ a ∈ A, a.kind.isSolid = true → touchN a = true → ¬ g₁.SameBlock (otherN a) y) ∨
        g₁.LabIn (newA 0) y) → g₁.HAvoid y := by
  have hle : ∀ u v, g₁.nBetween u v ≤ (A.filter fun a => a.kind.isSolid &&
      decide ((g₁.SameBlock a.x u ∧ g₁.SameBlock a.y v) ∨
        (g₁.SameBlock a.x v ∧ g₁.SameBlock a.y u))).length := by
    intro u v
    unfold Graph.nBetween
    refine le_trans (le_of_eq ?_) (hsub.filter (fun a => a.kind.isSolid &&
      decide ((g₁.SameBlock a.x u ∧ g₁.SameBlock a.y v) ∨
        (g₁.SameBlock a.x v ∧ g₁.SameBlock a.y u)))).length_le
    congr 1
    apply List.filter_congr
    intro c hc
    rw [(Graph.mem_unpart.1 hc).2.1]
    rfl
  have hα : ∀ u, g₁.SameBlock u (newA 0) → u = newA 0 :=
    fun u h => (hnew u).1 (Graph.sameBlock_symm h)
  have hfar : ∀ u v, ¬ g₁.SameBlock u (newA 0) → ¬ g₁.SameBlock v (newA 0) →
      g₁.nBetween u v ≤ 1 := by
    intro u v hu hv
    refine (hle u v).trans (le_trans (filter_length_le_of _ _ _ fun a _ ha => ?_) hN)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
    simp only [Bool.and_eq_true, Bool.not_eq_true', ha.1, true_and]
    unfold touchN
    by_contra hne
    simp only [Bool.not_eq_false, Bool.or_eq_true, beq_iff_eq] at hne
    rcases ha.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hne with h | h
    · rw [h] at h1; exact hu (Graph.sameBlock_symm h1)
    · rw [h] at h2; exact hv (Graph.sameBlock_symm h2)
    · rw [h] at h1; exact hv (Graph.sameBlock_symm h1)
    · rw [h] at h2; exact hu (Graph.sameBlock_symm h2)
  have hnear : ∀ v, ¬ g₁.SameBlock (newA 0) v →
      g₁.nBetween (newA 0) v ≤ (A.filter fun a => a.kind.isSolid && touchN a &&
        decide (g₁.SameBlock (otherN a) v)).length := by
    intro v hv
    refine (hle _ v).trans (filter_length_le_of _ _ _ fun a ha h => ?_)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    obtain ⟨hs, hb⟩ := h
    have hne := hAb a ha hs
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hα _ h1
      refine ⟨⟨hs, by simp [touchN, this]⟩, ?_⟩
      simp only [otherN, this, if_true]; exact h2
    · have := hα _ h2
      have hx : a.x ≠ newA 0 := fun h => hne (h.trans this.symm)
      refine ⟨⟨hs, by simp [touchN, this]⟩, ?_⟩
      simp only [otherN, hx, if_false]; exact h1
  have hnear2 : ∀ v, ¬ g₁.SameBlock (newA 0) v → g₁.nBetween (newA 0) v ≤ 2 := by
    intro v hv
    refine (hnear v hv).trans (le_trans (filter_length_le_of _ _ _ fun a _ h => ?_) hT)
    simp only [Bool.and_eq_true] at h ⊢
    exact h.1
  have hcases : ∀ u v, ¬ g₁.SameBlock u v →
      g₁.nBetween u v ≤ 1 ∨ (u = newA 0 ∧ ¬ g₁.SameBlock (newA 0) v) ∨
        (v = newA 0 ∧ ¬ g₁.SameBlock (newA 0) u) := by
    intro u v huv
    by_cases hu : g₁.SameBlock u (newA 0)
    · have := hα u hu
      subst this
      exact Or.inr (Or.inl ⟨rfl, huv⟩)
    · by_cases hv : g₁.SameBlock v (newA 0)
      · have := hα v hv
        subst this
        exact Or.inr (Or.inr ⟨rfl, fun h => huv (Graph.sameBlock_symm h)⟩)
      · exact Or.inl (hfar u v hu hv)
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    rcases hcases u v huv with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · omega
    · exact hnear2 v h
    · rw [Graph.nBetween_comm]; exact hnear2 u h
  · intro hpw
    have hone : ∀ v, (A.filter fun a => a.kind.isSolid && touchN a &&
        decide (g₁.SameBlock (otherN a) v)).length ≤ 1 := by
      intro v
      have := length_filter_le_one_of_pairwise hpw (fun b => decide (g₁.SameBlock b v))
        (fun a b ha hb hab => by
          simp only [decide_eq_true_eq] at ha hb
          exact hab (Graph.sameBlock_trans ha (Graph.sameBlock_symm hb)))
      rw [List.filter_map, List.length_map, List.filter_filter] at this
      refine le_trans (le_of_eq ?_) this
      congr 1
      apply List.filter_congr
      intro a _
      simp only [Function.comp_apply]
      rw [Bool.and_comm]
    intro u v huv
    rcases hcases u v huv with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact h
    · exact (hnear v h).trans (hone v)
    · rw [Graph.nBetween_comm]; exact (hnear u h).trans (hone u)
  · intro y hy hcond u v huv h2
    have hzero : ∀ w, g₁.SameBlock w y → (∀ a ∈ A, a.kind.isSolid = true → touchN a = true →
        ¬ g₁.SameBlock (otherN a) y) → (A.filter fun a => a.kind.isSolid && touchN a &&
          decide (g₁.SameBlock (otherN a) w)).length = 0 := by
      intro w hw hH
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro a ha h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact hH a ha h.1.1 h.1.2 (Graph.sameBlock_trans h.2 hw)
    rcases hcases u v huv with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · omega
    · by_cases hv : g₁.SameBlock v y
      · rcases hcond with hH | hH
        · have := (hnear v h).trans (le_of_eq (hzero v hv hH)); omega
        · exact Or.inr (Or.inr ⟨hv, hH.congr_right (Graph.sameBlock_symm hv)⟩)
      · exact Or.inl ⟨hy, hv⟩
    · by_cases hu : g₁.SameBlock u y
      · rcases hcond with hH | hH
        · rw [Graph.nBetween_comm] at h2
          have := (hnear u h).trans (le_of_eq (hzero u hu hH)); omega
        · exact Or.inr (Or.inl ⟨hu, hH.congr_right (Graph.sameBlock_symm hu)⟩)
      · exact Or.inl ⟨hu, hy⟩

end ShapeBeta

/-! ## The clauses on a term with one new atom -/

section ShapeTerm

variable {k n : ℕ}

theorem length_filter_split {α : Type*} (L : List α) (p q : α → Bool) :
    (L.filter p).length = (L.filter fun a => p a && !q a).length +
      (L.filter fun a => p a && q a).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.filter_cons]
    cases p a <;> cases q a <;> simp [ih] <;> omega

/-- A term with one new atom obtained by removing the labelled components `R` and adding the
components `A` has the clauses `PStepsTermOK`, if the scaling order does not drop, and if it is unchanged
the weighted number of labelled weights and edge ends at the block of `x` drops and the edges at
the new atom go to distinct blocks, or not to the block of `x`, or are the only labelled
components at the new atom and go to the block of `x`. -/
theorem termOfShape {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {R rest : List (Comp (Atom k n))} (hR : g.comps.Perm (R ++ rest))
    {A : List (Comp (Atom k (n + 1)))} {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++ A))
    (hlt : LTOut C x g A g₁) (hA4 : A.length ≤ 4)
    (hAb : ∀ a ∈ A, a.kind.isSolid = true → a.x ≠ a.y)
    (hN : (A.filter fun a => a.kind.isSolid && !touchN a).length ≤ 1)
    (hT : (A.filter fun a => a.kind.isSolid && touchN a).length ≤ 2)
    (hord : psteps_ordL R + 2 ≤ psteps_ordL A)
    (heq : psteps_ordL A = psteps_ordL R + 2 →
      (A.map (wBP fun u => g₁.SameBlock u (liftA 1 x))).sum <
        (R.map (wBP fun u => g.SameBlock u x)).sum ∧
      (((A.filter fun a => a.kind.isSolid && touchN a).map otherN).Pairwise
          (fun a b => ¬ g₁.SameBlock a b) ∨
        (∀ a ∈ A, a.kind.isSolid = true → touchN a = true →
          ¬ g₁.SameBlock (otherN a) (liftA 1 x)) ∨
        g₁.LabIn (newA 0) (liftA 1 x))) :
    PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
  obtain ⟨hB2, hB1, hHA⟩ := shapeBeta hlt.unpSub hlt.blkNew hAb hN hT
  have hunp : g₁.unpart.length ≤ 3 := by
    refine hlt.unp.trans ?_
    rw [length_filter_split A (fun a => a.kind.isSolid) touchN]
    omega
  have hsz := hS.nn.reg.size
  have hord' := ord_lift (g := g) hR hL
  have hpw := pw_lift (x := x) hR hL hlt.blk
  have hαx : ¬ g₁.SameBlock (newA 0) (liftA 1 x) := fun h =>
    liftA_ne_newA 1 x 0 ((hlt.blkNew _).1 h)
  refine ⟨hlt.nn.mono (by omega), hunp, ?_, hB2, hlt.sr, ?_, ?_⟩
  · have := hlt.orp
    show g₁.unpart.length + g₁.orph.length ≤ C + 5
    omega
  · show g.ord ≤ g₁.ord
    rw [hord']; linarith
  · intro he
    change g₁.ord = g.ord at he
    rw [hord'] at he
    obtain ⟨hlt', hc⟩ := heq (by linarith)
    refine ⟨?_, ?_⟩
    · show g₁.pw (liftA 1 x) < g.pw x
      omega
    · rcases hc with hc | hc | hc
      · exact Or.inl (hB1 hc)
      · exact Or.inr (hHA _ hαx (Or.inl hc))
      · exact Or.inr (hHA _ hαx (Or.inr hc))

end ShapeTerm

/-! ## Terms with one new atom: the general form -/

section TermGen

variable {k n : ℕ}

/-- The conditions on one added component of a term with one new atom: not a dotted or
`×`-dotted edge, labelled `P` at the image of `x` exactly when random, plain and well formed, a
solid edge joins two distinct atoms not in one block and has an internal end. -/
def AOK (x : Atom k n) (g : Graph k n) (a : Comp (Atom k (n + 1))) : Prop :=
  (a.kind ≠ .dot ∧ a.kind ≠ .xdot) ∧
  a.label = (if a.kind.isRandom then some (.P, liftA 1 x) else none) ∧
  (a.minor = [] ∧ (∀ ch, a.kind ≠ .inv ch) ∧ (∀ ch d, a.kind ≠ .wD ch d) ∧
    (a.kind.isWeight = true → a.y = a.x)) ∧
  (a.kind.isSolid = true → a.x ≠ a.y ∧
    ∀ u v, a.x = liftA 1 u → a.y = liftA 1 v → ¬ g.SameBlock u v) ∧
  (a.kind.isSolid = true → a.x.isRight = true ∨ a.y.isRight = true)

theorem bconn_of_G {m : ℕ} {g₁ : Graph k m} {d : Comp (Atom k m)} (hd : d ∈ g₁.comps)
    (hk : d.kind = .G .plus) {a b : Fin m} (hx : d.x = .inr a) (hy : d.y = .inr b) :
    Relation.EqvGen (bconn g₁) a b :=
  Relation.EqvGen.rel _ _ (Or.inr ⟨d, hd, hk, hx, hy⟩)

theorem bconn_of_mol {m : ℕ} {g₁ : Graph k m} {d : Comp (Atom k m)} (hd : d ∈ g₁.comps)
    (hk : d.kind.joinsMol = true) {a b : Fin m} (hx : d.x = .inr a) (hy : d.y = .inr b) :
    Relation.EqvGen (bconn g₁) a b := by
  refine Relation.EqvGen.rel _ _ (Or.inl ?_)
  by_cases hab : a = b
  · exact Or.inl (by rw [hab])
  · refine Or.inr ⟨rfl, rfl, SimpleGraph.Adj.reachable ?_⟩
    rw [Graph.molGraph, SimpleGraph.fromRel_adj]
    exact ⟨by simpa using hab, Or.inl ⟨d, hd, hk, hx, hy⟩⟩

/-- A term with one new atom whose added components satisfy `AOK` has the clauses `PStepsTermOK` under
the conditions of `termOfShape`. -/
theorem termGen {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {R rest : List (Comp (Atom k n))} (hR : g.comps.Perm (R ++ rest))
    (hRl : ∀ c ∈ R, c.label = some (.P, x))
    {A : List (Comp (Atom k (n + 1)))} {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++ A))
    (hAOK : ∀ a ∈ A, AOK x g a)
    (hAs : mkC (.waved .s) (liftA 1 x) (newA 0) ∈ A)
    (hcon : ∀ c ∈ R, Relation.EqvGen
      (fun u v => ∃ d ∈ g₁.comps, d.kind ≠ .xdot ∧ d.x = u ∧ d.y = v) (liftA 1 c.x) (liftA 1 c.y))
    (hblue : ∀ c ∈ R, c.kind = .G .plus → ∀ a b, c.x = .inr a → c.y = .inr b →
      Relation.EqvGen (bconn g₁) (Fin.castAdd 1 a) (Fin.castAdd 1 b))
    (hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩)
    (hA4 : A.length ≤ 4)
    (hN : (A.filter fun a => a.kind.isSolid && !touchN a).length ≤ 1)
    (hT : (A.filter fun a => a.kind.isSolid && touchN a).length ≤ 2)
    (hord : psteps_ordL R + 2 ≤ psteps_ordL A)
    (heq : psteps_ordL A = psteps_ordL R + 2 → LTOut C x g A g₁ →
      (A.map (wBP fun u => g₁.SameBlock u (liftA 1 x))).sum <
        (R.map (wBP fun u => g.SameBlock u x)).sum ∧
      (((A.filter fun a => a.kind.isSolid && touchN a).map otherN).Pairwise
          (fun a b => ¬ g₁.SameBlock a b) ∨
        (∀ a ∈ A, a.kind.isSolid = true → touchN a = true →
          ¬ g₁.SameBlock (otherN a) (liftA 1 x)) ∨
        g₁.LabIn (newA 0) (liftA 1 x))) :
    PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
  have hlt : LTOut C x g A g₁ := liftTerm hS hR hRl hL (fun a ha => (hAOK a ha).1)
    (fun a ha => (hAOK a ha).2.1) (fun a ha => (hAOK a ha).2.2.1) hAs
    (fun a ha => (hAOK a ha).2.2.2.1) (fun a ha => (hAOK a ha).2.2.2.2) hcon hblue hch
  exact termOfShape hS hR hL hlt hA4 (fun a ha hs => ((hAOK a ha).2.2.2.1 hs).1) hN hT hord
    (fun h => heq h hlt)

/-- `LabIn` at the new atom from the added components. -/
theorem labIn_new {g₁ : Graph k (n + 1)} {rest : List (Comp (Atom k n))}
    {A : List (Comp (Atom k (n + 1)))}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++ A))
    (hnew : ∀ b, g₁.SameBlock (newA 0) b ↔ b = newA 0) {y : Atom k (n + 1)}
    (hA : ∀ a ∈ A, a.label.isSome = true → (a.x = newA 0 ∨ a.y = newA 0) →
      a.kind.isSolid = true ∧
        ((a.x = newA 0 ∧ g₁.SameBlock a.y y) ∨ (g₁.SameBlock a.x y ∧ a.y = newA 0))) :
    g₁.LabIn (newA 0) y := by
  intro c hc hl hca
  have hca' : c.x = newA 0 ∨ c.y = newA 0 := by
    rcases hca with h | h
    · exact Or.inl ((hnew _).1 (Graph.sameBlock_symm h))
    · exact Or.inr ((hnew _).1 (Graph.sameBlock_symm h))
  rcases List.mem_append.1 (hL.subset hc) with h | h
  · exfalso
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 h
    rcases hca' with h' | h' <;> exact liftA_ne_newA 1 _ 0 h'
  · obtain ⟨hs, h1 | h1⟩ := hA c h hl hca'
    · exact ⟨hs, Or.inl ⟨by rw [h1.1]; exact Graph.sameBlock_refl _ _, h1.2⟩⟩
    · exact ⟨hs, Or.inr ⟨h1.1, by rw [h1.2]; exact Graph.sameBlock_refl _ _⟩⟩

end TermGen

/-! ## Terms with one new atom: the added components -/

section TermElems

variable {k n : ℕ}

theorem aok_G {x : Atom k n} {g : Graph k n} {a : Comp (Atom k (n + 1))} {ch : Charge}
    (hk : a.kind = .G ch) (hm : a.minor = []) (hl : a.label = some (.P, liftA 1 x))
    (hne : a.x ≠ a.y) (hb : ∀ u v, a.x = liftA 1 u → a.y = liftA 1 v → ¬ g.SameBlock u v)
    (hi : a.x.isRight = true ∨ a.y.isRight = true) : AOK x g a :=
  ⟨⟨by rw [hk]; simp, by rw [hk]; simp⟩, by rw [hl, hk]; simp [Kind.isRandom],
    ⟨hm, by rw [hk]; simp, by rw [hk]; simp, by rw [hk]; simp [Kind.isWeight]⟩,
    fun _ => ⟨hne, hb⟩, fun _ => hi⟩

theorem aok_W {x : Atom k n} {g : Graph k n} {a : Comp (Atom k (n + 1))} {ch : Charge}
    (hk : a.kind = .weight ch ∨ a.kind = .light ch) (hm : a.minor = [])
    (hl : a.label = some (.P, liftA 1 x)) (hy : a.y = a.x) : AOK x g a := by
  rcases hk with hk | hk <;>
  exact ⟨⟨by rw [hk]; simp, by rw [hk]; simp⟩, by rw [hl, hk]; simp [Kind.isRandom],
    ⟨hm, by rw [hk]; simp, by rw [hk]; simp, fun _ => hy⟩, by rw [hk]; simp [Kind.isSolid],
    by rw [hk]; simp [Kind.isSolid]⟩

theorem aok_sx {x : Atom k n} {g : Graph k n} :
    AOK x g (mkC (.waved .s) (liftA 1 x) (newA 0)) :=
  ⟨⟨by simp [mkC], by simp [mkC]⟩, by simp [mkC, Kind.isRandom],
    ⟨rfl, by simp [mkC], by simp [mkC], by simp [mkC, Kind.isWeight]⟩, by simp [mkC, Kind.isSolid],
    by simp [mkC, Kind.isSolid]⟩

/-- A solid edge from the new atom to an old atom satisfies `AOK`. -/
theorem aok_Gnew {x : Atom k n} {g : Graph k n} {a : Comp (Atom k (n + 1))} {ch : Charge}
    {z : Atom k n} (hk : a.kind = .G ch) (hm : a.minor = []) (hl : a.label = some (.P, liftA 1 x))
    (he : (a.x = newA 0 ∧ a.y = liftA 1 z) ∨ (a.x = liftA 1 z ∧ a.y = newA 0)) : AOK x g a := by
  refine aok_G hk hm hl ?_ ?_ ?_
  · rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact (liftA_ne_newA 1 z 0).symm
    · exact liftA_ne_newA 1 z 0
  · intro u v hu hv
    exfalso
    rcases he with ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [h1] at hu; exact liftA_ne_newA 1 u 0 hu.symm
    · rw [h2] at hv; exact liftA_ne_newA 1 v 0 hv.symm
  · rcases he with ⟨h1, -⟩ | ⟨-, h2⟩
    · left; rw [h1]; rfl
    · right; rw [h2]; rfl

open Classical in
theorem wBP_G {B : Atom k n → Prop} {a : Comp (Atom k n)} {ch : Charge}
    (hk : a.kind = .G ch) (hl : a.label.isSome = true) :
    wBP B a = (if B a.x then 1 else 0) + (if B a.y then 1 else 0) := by
  unfold wBP; rw [if_pos hl, hk]

open Classical in
theorem wBP_W {B : Atom k n → Prop} {a : Comp (Atom k n)} {ch : Charge}
    (hk : a.kind = .weight ch) (hl : a.label.isSome = true) :
    wBP B a = if B a.x then 1 else 0 := by
  unfold wBP; rw [if_pos hl, hk]

open Classical in
theorem wBP_L {B : Atom k n → Prop} {a : Comp (Atom k n)} {ch : Charge}
    (hk : a.kind = .light ch) (hl : a.label.isSome = true) :
    wBP B a = if B a.x then 4 else 0 := by
  unfold wBP; rw [if_pos hl, hk]

theorem wBP_none {B : Atom k n → Prop} {a : Comp (Atom k n)} (hl : a.label = none) :
    wBP B a = 0 := by
  unfold wBP; rw [hl]; rfl

theorem wBP_det {B : Atom k n → Prop} {a : Comp (Atom k n)}
    (hk : a.kind.isRandom = false) : wBP B a = 0 := by
  rcases a with ⟨κ, a, b, mi, l⟩
  cases κ <;> simp_all [wBP, Kind.isRandom]

end TermElems

/-! ## Paths in a graph with one new atom -/

section Paths

variable {k : ℕ}

/-- Two internal atoms joined by a path of molecules and solid edges `G` of charge `plus`. -/
def BB {m : ℕ} (g₁ : Graph k m) (u v : Atom k m) : Prop :=
  ∃ a b, u = .inr a ∧ v = .inr b ∧ Relation.EqvGen (bconn g₁) a b

theorem BB.trans {m : ℕ} {g₁ : Graph k m} {u v w : Atom k m} (h1 : BB g₁ u v)
    (h2 : BB g₁ v w) : BB g₁ u w := by
  obtain ⟨a, b, rfl, rfl, h⟩ := h1
  obtain ⟨b', c, hb, rfl, h'⟩ := h2
  cases Sum.inr.inj hb
  exact ⟨a, c, rfl, rfl, h.trans _ _ _ h'⟩

theorem BB.symm {m : ℕ} {g₁ : Graph k m} {u v : Atom k m} (h : BB g₁ u v) : BB g₁ v u := by
  obtain ⟨a, b, rfl, rfl, h⟩ := h
  exact ⟨b, a, rfl, rfl, h.symm⟩

theorem BB.ends {m : ℕ} {g₁ : Graph k m} {d : Comp (Atom k m)} {p q : Atom k m}
    (he : (d.x = p ∧ d.y = q) ∨ (d.x = q ∧ d.y = p)) (h : BB g₁ d.x d.y) : BB g₁ p q := by
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at h; exact h
  · rw [h1, h2] at h; exact h.symm

theorem BB_of_G {m : ℕ} {g₁ : Graph k m} {d : Comp (Atom k m)} (hd : d ∈ g₁.comps)
    (hk : d.kind = .G .plus) (hx : d.x.isRight = true) (hy : d.y.isRight = true) :
    BB g₁ d.x d.y := by
  rcases hdx : d.x with a | a
  · rw [hdx] at hx; cases hx
  rcases hdy : d.y with b | b
  · rw [hdy] at hy; cases hy
  exact ⟨a, b, rfl, rfl, bconn_of_G hd hk hdx hdy⟩

theorem BB_of_mol {m : ℕ} {g₁ : Graph k m} {d : Comp (Atom k m)} (hd : d ∈ g₁.comps)
    (hk : d.kind.joinsMol = true) (hx : d.x.isRight = true) (hy : d.y.isRight = true) :
    BB g₁ d.x d.y := by
  rcases hdx : d.x with a | a
  · rw [hdx] at hx; cases hx
  rcases hdy : d.y with b | b
  · rw [hdy] at hy; cases hy
  exact ⟨a, b, rfl, rfl, bconn_of_mol hd hk hdx hdy⟩

theorem BB.refl {m : ℕ} {g₁ : Graph k m} {u : Atom k m} (hu : u.isRight = true) :
    BB g₁ u u := by
  rcases u with a | a
  · cases hu
  · exact ⟨a, a, rfl, rfl, Relation.EqvGen.refl _⟩

/-- The relation of the paths without `×`-dotted edges. -/
def NX {m : ℕ} (g₁ : Graph k m) : Atom k m → Atom k m → Prop :=
  Relation.EqvGen fun u v => ∃ d ∈ g₁.comps, d.kind ≠ .xdot ∧ d.x = u ∧ d.y = v

theorem NX.ends {m : ℕ} {g₁ : Graph k m} {d : Comp (Atom k m)} (hd : d ∈ g₁.comps)
    (hk : d.kind ≠ .xdot) {p q : Atom k m} (he : (d.x = p ∧ d.y = q) ∨ (d.x = q ∧ d.y = p)) :
    NX g₁ p q := by
  have h : NX g₁ d.x d.y := Relation.EqvGen.rel _ _ ⟨d, hd, hk, rfl, rfl⟩
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at h; exact h
  · rw [h1, h2] at h; exact h.symm

end Paths

theorem ite_len_le_one {α : Type*} (p : Prop) [Decidable p] (a : α) :
    (if p then [a] else []).length ≤ 1 := by
  split <;> simp

/-! ## Derivative terms with one new atom -/

section TermD

variable {k n : ℕ}

/-- A derivative term: `r` (a light weight at `x`, or a solid edge between `x` and `z`) and `c`
removed; a solid edge `e` between the new atom and `z`, a solid edge `αp` from the new atom to one
end `w` of `c` and a component `xp` from `x` to the other end `v` (a weight if `v = x`) added,
with the waved edge between `x` and the new atom. -/
theorem termD' {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {r c : Comp (Atom k n)} {rest : List (Comp (Atom k n))}
    (hR : g.comps.Perm ([r, c] ++ rest))
    (hrl : r.label = some (.P, x)) (hcl : c.label = some (.P, x))
    {z : Atom k n} (hz : z = x ∨ ¬ g.SameBlock z x) {ch : Charge}
    (hr : (r.kind = .light ch ∧ r.x = x ∧ z = x) ∨
      (r.kind = .G ch ∧ ((r.x = x ∧ r.y = z) ∨ (r.x = z ∧ r.y = x))))
    (hcx : c.kind.isSolid = true → (c.x = x ∨ c.y = x) → z = x ∧ r.kind.isWeight = true)
    {cc : Charge} (hck : c.kind = .G cc ∨ c.kind = .weight cc ∨ c.kind = .light cc)
    {w v : Atom k n} (hwv : (w = c.x ∧ v = c.y) ∨ (w = c.y ∧ v = c.x))
    {αp xp e : Comp (Atom k (n + 1))}
    (hαp : αp.kind = .G cc ∧ αp.minor = [] ∧ αp.label = some (.P, liftA 1 x) ∧
      ((αp.x = newA 0 ∧ αp.y = liftA 1 w) ∨ (αp.x = liftA 1 w ∧ αp.y = newA 0)))
    (hxp : xp.kind = (if v = x then .weight cc else .G cc) ∧ xp.minor = [] ∧
      xp.label = some (.P, liftA 1 x) ∧
      ((xp.x = liftA 1 x ∧ xp.y = liftA 1 v) ∨ (xp.x = liftA 1 v ∧ xp.y = liftA 1 x)))
    (he : e.kind = .G ch ∧ e.minor = [] ∧ e.label = some (.P, liftA 1 x) ∧
      ((e.x = newA 0 ∧ e.y = liftA 1 z) ∨ (e.x = liftA 1 z ∧ e.y = newA 0)))
    {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++
      [αp, xp, mkC (.waved .s) (liftA 1 x) (newA 0), e]))
    (hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩) :
    PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
  classical
  have hN := hS.nn
  have hcm : c ∈ g.comps := hR.symm.subset (by simp)
  have hrm : r ∈ g.comps := hR.symm.subset (by simp)
  have hx₁ : (liftA 1 x).isRight = true := by rw [liftA_isRight]; exact hN.hx
  have hS6c := hS.s6 c hcm (by rw [hcl]; rfl)
  have hplc := hN.plain c hcm
  have hcy : c.kind.isWeight = true → c.y = c.x := hplc.2.2.2.2.1
  have hvx : v = x ∨ ¬ g.SameBlock v x := by
    by_cases h : g.SameBlock v x
    · left
      rcases hwv with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hS6c.2 h
      · exact hS6c.1 h
    · exact Or.inr h
  set sx : Comp (Atom k (n + 1)) := mkC (.waved .s) (liftA 1 x) (newA 0) with hsx
  have hmem : ∀ a ∈ [αp, xp, sx, e], a ∈ g₁.comps := fun a ha =>
    hL.symm.subset (List.mem_append_right _ ha)
  have hαm := hmem αp (by simp)
  have hxm := hmem xp (by simp)
  have hsm := hmem sx (by simp)
  have hem := hmem e (by simp)
  -- the added components
  have hxpA : AOK x g xp := by
    by_cases hv : v = x
    · rw [if_pos hv] at hxp
      refine aok_W (Or.inl hxp.1) hxp.2.1 hxp.2.2.1 ?_
      rcases hxp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, hv]
    · rw [if_neg hv] at hxp
      have hvx' : ¬ g.SameBlock v x := hvx.resolve_left hv
      refine aok_G hxp.1 hxp.2.1 hxp.2.2.1 ?_ ?_ ?_
      · rcases hxp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> intro h
        · exact hv (liftA_injective 1 h).symm
        · exact hv (liftA_injective 1 h)
      · intro u u' hu hu'
        rcases hxp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1] at hu; rw [h2] at hu'
          rw [← liftA_injective 1 hu, ← liftA_injective 1 hu']
          exact fun h => hvx' (Graph.sameBlock_symm h)
        · rw [h1] at hu; rw [h2] at hu'
          rw [← liftA_injective 1 hu, ← liftA_injective 1 hu']
          exact hvx'
      · rcases hxp.2.2.2 with ⟨h1, -⟩ | ⟨-, h2⟩
        · left; rw [h1]; exact hx₁
        · right; rw [h2]; exact hx₁
  have hAOK : ∀ a ∈ [αp, xp, sx, e], AOK x g a := by
    intro a ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact aok_Gnew hαp.1 hαp.2.1 hαp.2.2.1 hαp.2.2.2
    · exact hxpA
    · exact aok_sx
    · exact aok_Gnew he.1 he.2.1 he.2.2.1 he.2.2.2
  -- counts
  have hαs : αp.kind.isSolid = true := by rw [hαp.1]; rfl
  have hes : e.kind.isSolid = true := by rw [he.1]; rfl
  have hsxs : sx.kind.isSolid = false := rfl
  have hαt : touchN αp = true := by
    unfold touchN; rcases hαp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  have het : touchN e = true := by
    unfold touchN; rcases he.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  have hxt : touchN xp = false := by
    unfold touchN
    rcases hxp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2, liftA_ne_newA]
  have hαo : otherN αp = liftA 1 w := by
    unfold otherN
    rcases hαp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos h1, h2]
    · rw [if_neg (by rw [h1]; exact liftA_ne_newA 1 w 0), h1]
  have heo : otherN e = liftA 1 z := by
    unfold otherN
    rcases he.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos h1, h2]
    · rw [if_neg (by rw [h1]; exact liftA_ne_newA 1 z 0), h1]
  have hTl : [αp, xp, sx, e].filter (fun a => a.kind.isSolid && touchN a) = [αp, e] := by
    simp [List.filter_cons, hαs, hαt, hxt, hsxs, hes, het]
  have hord_r : r.kind.ord = 1 := by
    rcases hr with ⟨hk, -⟩ | ⟨hk, -⟩ <;> rw [hk] <;> rfl
  have hord_c : c.kind.ord ≤ 1 := by
    rcases hck with hk | hk | hk <;> rw [hk] <;> simp [Kind.ord]
  have hord_x : xp.kind.ord = if v = x then 0 else 1 := by
    rw [hxp.1]; split_ifs <;> rfl
  have hordR : psteps_ordL [r, c] = 1 + c.kind.ord := by simp [psteps_ordL, hord_r]
  have hordA : psteps_ordL [αp, xp, sx, e] = 4 + xp.kind.ord := by
    simp only [psteps_ordL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hαp.1, he.1, hsx,
      mkC]
    simp only [Kind.ord]; ring
  -- paths
  have hNXs : NX g₁ (liftA 1 x) (newA 0) := NX.ends hsm (by simp [hsx, mkC]) (Or.inl ⟨rfl, rfl⟩)
  have hNXe : NX g₁ (newA 0) (liftA 1 z) := NX.ends hem (by rw [he.1]; simp) he.2.2.2
  have hNXα : NX g₁ (newA 0) (liftA 1 w) := NX.ends hαm (by rw [hαp.1]; simp) hαp.2.2.2
  have hNXx : NX g₁ (liftA 1 x) (liftA 1 v) := by
    refine NX.ends hxm ?_ hxp.2.2.2
    rw [hxp.1]; split_ifs <;> simp
  have hBs : BB g₁ (liftA 1 x) (newA 0) :=
    BB.ends (d := sx) (Or.inl ⟨rfl, rfl⟩) (BB_of_mol hsm rfl hx₁ newA_isRight)
  refine termGen hS hR ?_ hL hAOK (by rw [hsx]; simp) ?_ ?_ hch (by simp) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl
    · exact hrl
    · exact hcl
  · intro a ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl
    · rcases hr with ⟨hk, -, -⟩ | ⟨hk, h⟩
      · have : a.y = a.x := (hN.plain a hrm).2.2.2.2.1 (by rw [hk]; rfl)
        rw [this]; exact Relation.EqvGen.refl _
      · have hp : NX g₁ (liftA 1 x) (liftA 1 z) := hNXs.trans _ _ _ hNXe
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact hp
        · rw [h1, h2]; exact hp.symm
    · have hp : NX g₁ (liftA 1 w) (liftA 1 v) :=
        hNXα.symm.trans _ _ _ (hNXs.symm.trans _ _ _ hNXx)
      rcases hwv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact hp
      · rw [← h1, ← h2]; exact hp.symm
  · intro a ha hk u u' hu hu'
    suffices BB g₁ (liftA 1 a.x) (liftA 1 a.y) by
      obtain ⟨p, q, hp, hq, h⟩ := this
      rw [hu, liftA_inr] at hp; rw [hu', liftA_inr] at hq
      cases Sum.inr.inj hp; cases Sum.inr.inj hq
      exact h
    have hai : a.x.isRight = true ∧ a.y.isRight = true := by rw [hu, hu']; exact ⟨rfl, rfl⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl
    · rcases hr with ⟨hk', -⟩ | ⟨hk', h⟩
      · rw [hk] at hk'; cases hk'
      · rw [hk] at hk'
        cases hk'
        have hzi : z.isRight = true := by
          rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
          · rw [← h2]; exact hai.2
          · rw [← h1]; exact hai.1
        have hBe : BB g₁ (newA 0) (liftA 1 z) :=
          BB.ends he.2.2.2 (BB_of_G hem he.1 (by
            rcases he.2.2.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
            · exact newA_isRight
            · rw [liftA_isRight]; exact hzi) (by
            rcases he.2.2.2 with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
            · rw [liftA_isRight]; exact hzi
            · exact newA_isRight))
        have hp := hBs.trans hBe
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact hp
        · rw [h1, h2]; exact hp.symm
    · have hcc : cc = .plus := by
        rcases hck with h | h | h <;> rw [hk] at h <;> cases h; rfl
      subst hcc
      have hwi : w.isRight = true := by
        rcases hwv with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
        · exact hai.1
        · exact hai.2
      have hvi : v.isRight = true := by
        rcases hwv with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
        · exact hai.2
        · exact hai.1
      have hBα : BB g₁ (newA 0) (liftA 1 w) :=
        BB.ends hαp.2.2.2 (BB_of_G hαm hαp.1 (by
          rcases hαp.2.2.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
          · exact newA_isRight
          · rw [liftA_isRight]; exact hwi) (by
          rcases hαp.2.2.2 with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
          · rw [liftA_isRight]; exact hwi
          · exact newA_isRight))
      have hBx : BB g₁ (liftA 1 x) (liftA 1 v) := by
        by_cases hv : v = x
        · rw [hv]; exact BB.refl hx₁
        · have hk' : xp.kind = .G .plus := by rw [hxp.1, if_neg hv]
          refine BB.ends hxp.2.2.2 (BB_of_G hxm hk' ?_ ?_)
          · rcases hxp.2.2.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
            · exact hx₁
            · rw [liftA_isRight]; exact hvi
          · rcases hxp.2.2.2 with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
            · rw [liftA_isRight]; exact hvi
            · exact hx₁
      have hp : BB g₁ (liftA 1 w) (liftA 1 v) := hBα.symm.trans (hBs.symm.trans hBx)
      rcases hwv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact hp
      · rw [← h1, ← h2]; exact hp.symm
  · simp only [List.filter_cons, List.filter_nil, hαs, hαt, hxt, hsxs, hes, het, Bool.not_true,
      Bool.and_false, Bool.not_false, Bool.and_true, Bool.false_and]
    exact ite_len_le_one _ _
  · rw [hTl]; simp
  · rw [hordR, hordA]
    have : (0 : ℤ) ≤ xp.kind.ord := by rw [hord_x]; split_ifs <;> norm_num
    linarith
  · intro heq hlt
    rw [hordR, hordA] at heq
    have hv : v = x := by
      by_contra hv
      rw [hord_x, if_neg hv] at heq
      linarith
    rw [hord_x, if_pos hv] at heq
    have hc1 : c.kind.ord = 1 := by linarith
    set B₁ : Atom k (n + 1) → Prop := fun u => g₁.SameBlock u (liftA 1 x) with hB₁
    have hαx : ¬ g₁.SameBlock (newA 0) (liftA 1 x) := fun h =>
      liftA_ne_newA 1 x 0 ((hlt.blkNew _).1 h)
    have hblk : ∀ u, g₁.SameBlock (liftA 1 u) (liftA 1 x) ↔ g.SameBlock u x := fun u => hlt.blk u x
    have hwA : wBP B₁ αp = if g.SameBlock w x then 1 else 0 := by
      rw [wBP_G hαp.1 (by rw [hαp.2.2.1]; rfl)]
      rcases hαp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
        simp only [hB₁, hαx, hblk, if_false] <;> simp
    have hwX : wBP B₁ xp = 1 := by
      have hk' : xp.kind = .weight cc := by rw [hxp.1, if_pos hv]
      rw [wBP_W hk' (by rw [hxp.2.2.1]; rfl)]
      have : xp.x = liftA 1 x := by
        rcases hxp.2.2.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]; rw [hv]
      rw [this, if_pos (Graph.sameBlock_refl _ _)]
    have hwS : wBP B₁ sx = 0 := wBP_none rfl
    have hwE : wBP B₁ e = if g.SameBlock z x then 1 else 0 := by
      rw [wBP_G he.1 (by rw [he.2.2.1]; rfl)]
      rcases he.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
        simp only [hB₁, hαx, hblk, if_false] <;> simp
    have hsumA : ([αp, xp, sx, e].map (wBP B₁)).sum ≤ 3 := by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hwA, hwX, hwS, hwE]
      split_ifs <;> omega
    have hcR : wBP (fun u => g.SameBlock u x) c ≤ ([r, c].map (wBP fun u => g.SameBlock u x)).sum := by
      simp
    have hrR : wBP (fun u => g.SameBlock u x) r ≤ ([r, c].map (wBP fun u => g.SameBlock u x)).sum := by
      simp
    rcases hck with hk | hk | hk
    · -- `c` a solid edge with an end at `x`
      have hcxx : c.x = x ∨ c.y = x := by
        rcases hwv with ⟨-, h2⟩ | ⟨-, h2⟩
        · right; rw [← h2, hv]
        · left; rw [← h2, hv]
      obtain ⟨hzx, hrw⟩ := hcx (by rw [hk]; rfl) hcxx
      have hrL : r.kind = .light ch ∧ r.x = x := by
        rcases hr with ⟨h1, h2, -⟩ | ⟨h1, -⟩
        · exact ⟨h1, h2⟩
        · rw [h1] at hrw; cases hrw
      have hw4 : wBP (fun u => g.SameBlock u x) r = 4 := by
        rw [wBP_L hrL.1 (by rw [hrl]; rfl), if_pos (by rw [hrL.2]; exact Graph.sameBlock_refl _ _)]
      have hwx : ¬ g.SameBlock w x := by
        have hib := hN.inBlk c hcm (by rw [hk]; rfl)
        rcases hwv with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1]; rw [← hv, h2]; exact hib
        · rw [h1]; rw [← hv, h2]; exact fun h => hib (Graph.sameBlock_symm h)
      have hsumA' : ([αp, xp, sx, e].map (wBP B₁)).sum = 2 := by
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hwA, hwX, hwS, hwE,
          if_neg hwx, hzx, if_pos (Graph.sameBlock_refl _ _)]
        rfl
      refine ⟨by omega, Or.inl ?_⟩
      rw [hTl]
      simp only [List.map_cons, List.map_nil, hαo, heo, hzx, List.pairwise_cons,
        List.mem_cons, List.mem_nil_iff, or_false, forall_eq, and_true,
        List.not_mem_nil, false_imp_iff, imp_true_iff]
      rw [hblk]; exact ⟨hwx, trivial, List.Pairwise.nil⟩
    · rw [hk] at hc1; simp [Kind.ord] at hc1
    · -- `c` a light weight at `x`
      have hcyx : c.y = c.x := hcy (by rw [hk]; rfl)
      have hcx' : c.x = x := by
        rcases hwv with ⟨-, h2⟩ | ⟨-, h2⟩
        · rw [← hcyx, ← h2, hv]
        · rw [← h2, hv]
      have hw' : w = x := by
        rcases hwv with ⟨h1, -⟩ | ⟨h1, -⟩
        · rw [h1, hcx']
        · rw [h1, hcyx, hcx']
      have hc4 : wBP (fun u => g.SameBlock u x) c = 4 := by
        rw [wBP_L hk (by rw [hcl]; rfl), if_pos (by rw [hcx']; exact Graph.sameBlock_refl _ _)]
      refine ⟨by omega, ?_⟩
      rcases hz with hzx | hzx
      · right; right
        refine labIn_new hL hlt.blkNew fun a ha hl hα => ?_
        rcases List.mem_append.1 ((List.perm_append_comm.trans hL.symm).symm.subset
            (hL.symm.subset (List.mem_append_right _ ha))) with h | h
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl
          · refine ⟨hαs, ?_⟩
            rcases hαp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨h1, by rw [h2, hw']; exact Graph.sameBlock_refl _ _⟩
            · exact Or.inr ⟨by rw [h1, hw']; exact Graph.sameBlock_refl _ _, h2⟩
          · exfalso
            rcases hxp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hα <;>
              rcases hα with h' | h' <;> exact liftA_ne_newA 1 _ 0 h'
          · simp [hsx, mkC] at hl
          · refine ⟨hes, ?_⟩
            rcases he.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨h1, by rw [h2, hzx]; exact Graph.sameBlock_refl _ _⟩
            · exact Or.inr ⟨by rw [h1, hzx]; exact Graph.sameBlock_refl _ _, h2⟩
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl
          · refine ⟨hαs, ?_⟩
            rcases hαp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨h1, by rw [h2, hw']; exact Graph.sameBlock_refl _ _⟩
            · exact Or.inr ⟨by rw [h1, hw']; exact Graph.sameBlock_refl _ _, h2⟩
          · exfalso
            rcases hxp.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hα <;>
              rcases hα with h' | h' <;> exact liftA_ne_newA 1 _ 0 h'
          · simp [hsx, mkC] at hl
          · refine ⟨hes, ?_⟩
            rcases he.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨h1, by rw [h2, hzx]; exact Graph.sameBlock_refl _ _⟩
            · exact Or.inr ⟨by rw [h1, hzx]; exact Graph.sameBlock_refl _ _, h2⟩
      · left
        rw [hTl]
        simp only [List.map_cons, List.map_nil, hαo, heo, hw', List.pairwise_cons,
          List.mem_cons, List.mem_nil_iff, or_false, forall_eq, and_true,
          List.not_mem_nil, false_imp_iff, imp_true_iff]
        rw [hlt.blk]; exact ⟨fun h => hzx (Graph.sameBlock_symm h), trivial, List.Pairwise.nil⟩

end TermD

/-! ## Derivative terms: the factors of `-∂_{h_{pq}}` -/

section TermD2

variable {k n : ℕ}

theorem dPieces_form {c : Comp (Atom k n)} (hcy : c.kind.isWeight = true → c.y = c.x)
    {p q : Atom k (n + 1)} {ps : List (Comp (Atom k (n + 1)))}
    (h : (c.map (liftA 1)).dPieces p q = some ps) :
    ∃ cc, (c.kind = .G cc ∨ c.kind = .weight cc ∨ c.kind = .light cc) ∧
      (ps = [solidC cc (liftA 1 c.x) p, solidC cc q (liftA 1 c.y)] ∨
       ps = [solidC cc (liftA 1 c.x) q, solidC cc p (liftA 1 c.y)]) := by
  rcases c with ⟨κ, a, b, mi, l⟩
  simp only at hcy ⊢
  cases κ with
  | G ch =>
    cases ch
    · refine ⟨.plus, Or.inl rfl, Or.inl ?_⟩
      simp [Comp.dPieces, Comp.map, Kind.isWeight] at h; exact h.symm
    · refine ⟨.minus, Or.inl rfl, Or.inr ?_⟩
      simp [Comp.dPieces, Comp.map, Kind.isWeight] at h; exact h.symm
  | weight ch =>
    have hb : b = a := hcy rfl
    subst hb
    cases ch
    · refine ⟨.plus, Or.inr (Or.inl rfl), Or.inl ?_⟩
      simp [Comp.dPieces, Comp.map, Kind.isWeight] at h; exact h.symm
    · refine ⟨.minus, Or.inr (Or.inl rfl), Or.inr ?_⟩
      simp [Comp.dPieces, Comp.map, Kind.isWeight] at h; exact h.symm
  | light ch =>
    have hb : b = a := hcy rfl
    subst hb
    cases ch
    · refine ⟨.plus, Or.inr (Or.inr rfl), Or.inl ?_⟩
      simp [Comp.dPieces, Comp.map, Kind.isWeight] at h; exact h.symm
    · refine ⟨.minus, Or.inr (Or.inr rfl), Or.inr ?_⟩
      simp [Comp.dPieces, Comp.map, Kind.isWeight] at h; exact h.symm
  | _ => simp [Comp.dPieces, Comp.map] at h

theorem xp_form (x : Atom k n) (cc : Charge) {a b v : Atom k n}
    (hab : (a = x ∧ b = v) ∨ (a = v ∧ b = x)) :
    (rl (liftA 1 x) (solidC cc (liftA 1 a) (liftA 1 b))).kind =
        (if v = x then .weight cc else .G cc) ∧
      (rl (liftA 1 x) (solidC cc (liftA 1 a) (liftA 1 b))).minor = [] ∧
      (rl (liftA 1 x) (solidC cc (liftA 1 a) (liftA 1 b))).label = some (.P, liftA 1 x) ∧
      (((rl (liftA 1 x) (solidC cc (liftA 1 a) (liftA 1 b))).x = liftA 1 x ∧
          (rl (liftA 1 x) (solidC cc (liftA 1 a) (liftA 1 b))).y = liftA 1 v) ∨
        ((rl (liftA 1 x) (solidC cc (liftA 1 a) (liftA 1 b))).x = liftA 1 v ∧
          (rl (liftA 1 x) (solidC cc (liftA 1 a) (liftA 1 b))).y = liftA 1 x)) := by
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] <;> by_cases h : v = x
  · subst h; simp [solidC, rl, mkC, Kind.isRandom]
  · simp [solidC, rl, mkC, Kind.isRandom, (liftA_injective (k := k) (n := n) 1).eq_iff, h,
      Ne.symm h]
  · subst h; simp [solidC, rl, mkC, Kind.isRandom]
  · simp [solidC, rl, mkC, Kind.isRandom, (liftA_injective (k := k) (n := n) 1).eq_iff, h,
      Ne.symm h]

theorem αp_form (x : Atom k n) (cc : Charge) {u w : Atom k (n + 1)} (z : Atom k n)
    (huw : (u = newA 0 ∧ w = liftA 1 z) ∨ (u = liftA 1 z ∧ w = newA 0)) :
    (rl (liftA 1 x) (solidC cc u w)).kind = .G cc ∧
      (rl (liftA 1 x) (solidC cc u w)).minor = [] ∧
      (rl (liftA 1 x) (solidC cc u w)).label = some (.P, liftA 1 x) ∧
      (((rl (liftA 1 x) (solidC cc u w)).x = newA 0 ∧
          (rl (liftA 1 x) (solidC cc u w)).y = liftA 1 z) ∨
        ((rl (liftA 1 x) (solidC cc u w)).x = liftA 1 z ∧
          (rl (liftA 1 x) (solidC cc u w)).y = newA 0)) := by
  have hne := liftA_ne_newA (k := k) 1 z 0
  rcases huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [solidC, rl, mkC, Kind.isRandom, Ne.symm hne]
  · simp [solidC, rl, mkC, Kind.isRandom, hne]

/-- A derivative term of `-∂_{h_{pq}}` at a labelled component `c`, with `{p, q}` the new atom
and the image of `x`, has the clauses `PStepsTermOK` (see `termD'`). -/
theorem termD {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {r c : Comp (Atom k n)} {rest : List (Comp (Atom k n))}
    (hR : g.comps.Perm ([r, c] ++ rest))
    (hrl : r.label = some (.P, x)) (hcl : c.label = some (.P, x))
    {z : Atom k n} (hz : z = x ∨ ¬ g.SameBlock z x) {ch : Charge}
    (hr : (r.kind = .light ch ∧ r.x = x ∧ z = x) ∨
      (r.kind = .G ch ∧ ((r.x = x ∧ r.y = z) ∨ (r.x = z ∧ r.y = x))))
    (hcx : c.kind.isSolid = true → (c.x = x ∨ c.y = x) → z = x ∧ r.kind.isWeight = true)
    {p q : Atom k (n + 1)} (hpq : (p = newA 0 ∧ q = liftA 1 x) ∨ (p = liftA 1 x ∧ q = newA 0))
    {ps : List (Comp (Atom k (n + 1)))} (hps : (c.map (liftA 1)).dPieces p q = some ps)
    {e₀ : Comp (Atom k (n + 1))}
    (he : (e₀.x = newA 0 ∧ e₀.y = liftA 1 z) ∨ (e₀.x = liftA 1 z ∧ e₀.y = newA 0))
    (hek : e₀ = solidC ch e₀.x e₀.y)
    {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++
      (ps ++ [mkC (.waved .s) (liftA 1 x) (newA 0), e₀]).map (rl (liftA 1 x))))
    (hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩) :
    PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
  have hcm : c ∈ g.comps := hR.symm.subset (by simp)
  have hcy := (hS.nn.plain c hcm).2.2.2.2.1
  obtain ⟨cc, hck, hps'⟩ := dPieces_form hcy hps
  have he' := αp_form x ch z he
  rw [← hek] at he'
  have hsx : rl (liftA 1 x) (mkC (.waved .s) (liftA 1 x) (newA 0)) =
      mkC (.waved .s) (liftA 1 x) (newA 0) := by simp [rl, mkC, Kind.isRandom]
  -- the two orders of the factors
  have key : ∀ s₁ s₂ : Atom k (n + 1), ((s₁ = newA 0 ∧ s₂ = liftA 1 x) ∨
      (s₁ = liftA 1 x ∧ s₂ = newA 0)) →
      ps = [solidC cc (liftA 1 c.x) s₁, solidC cc s₂ (liftA 1 c.y)] →
      PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
    intro s₁ s₂ hs hps₁
    rw [hps₁] at hL
    simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, hsx] at hL
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact termD' hS hR hrl hcl hz hr hcx hck (Or.inl ⟨rfl, rfl⟩)
        (αp_form x cc c.x (Or.inr ⟨rfl, rfl⟩)) (xp_form x cc (Or.inl ⟨rfl, rfl⟩)) he' hL hch
    · have hL' := hL.trans (List.Perm.append_left _ (List.Perm.swap _ _ _))
      exact termD' hS hR hrl hcl hz hr hcx hck (Or.inr ⟨rfl, rfl⟩)
        (αp_form x cc c.y (Or.inl ⟨rfl, rfl⟩)) (xp_form x cc (Or.inr ⟨rfl, rfl⟩)) he' hL' hch
  rcases hps' with h | h
  · exact key p q hpq h
  · exact key q p (by rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
                      · exact Or.inr ⟨h2, h1⟩
                      · exact Or.inl ⟨h2, h1⟩) h

end TermD2

/-! ## [II, (4.23)] inside `P_x`: the terms -/

section RoundL

variable {k n : ℕ}

/-- The terms of [II, (4.23)] without derivative: a light weight on the new atom added, and a
light weight on `x` removed or not. -/
theorem termLa {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {R rest : List (Comp (Atom k n))} (hR : g.comps.Perm (R ++ rest))
    (hRl : ∀ c ∈ R, c.label = some (.P, x))
    (hR' : R = [] ∨ ∃ ℓ ch', R = [ℓ] ∧ ℓ.kind = .light ch' ∧ ℓ.x = x) {ch : Charge}
    {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++
      [mkC (.waved .s) (liftA 1 x) (newA 0), rl (liftA 1 x) (mkC (.light ch) (newA 0) (newA 0))]))
    (hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩) :
    PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
  have hla : rl (liftA 1 x) (mkC (.light ch) (newA 0) (newA 0)) =
      ⟨.light ch, newA 0, newA 0, [], some (.P, liftA 1 x)⟩ := by
    simp [rl, mkC, Kind.isRandom]
  rw [hla] at hL
  set la : Comp (Atom k (n + 1)) := ⟨.light ch, newA 0, newA 0, [], some (.P, liftA 1 x)⟩
  set sx : Comp (Atom k (n + 1)) := mkC (.waved .s) (liftA 1 x) (newA 0) with hsx
  have hRm : ∀ c ∈ R, c ∈ g.comps := fun c hc => hR.symm.subset (List.mem_append_left _ hc)
  have hR1 : ∀ c ∈ R, c.kind.isWeight = true := by
    intro c hc
    rcases hR' with rfl | ⟨ℓ, ch', rfl, hk, -⟩
    · simp at hc
    · rw [List.mem_singleton] at hc; subst hc; rw [hk]; rfl
  refine termGen hS hR hRl hL ?_ (by rw [hsx]; simp) ?_ ?_ hch (by simp) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl
    · exact aok_sx
    · exact aok_W (Or.inr rfl) rfl rfl rfl
  · intro c hc
    have : c.y = c.x := (hS.nn.plain c (hRm c hc)).2.2.2.2.1 (hR1 c hc)
    rw [this]; exact Relation.EqvGen.refl _
  · intro c hc hk
    have := hR1 c hc
    rw [hk] at this; cases this
  · simp [hsx, la, mkC, Kind.isSolid]
  · simp [hsx, la, mkC, Kind.isSolid]
  · have : psteps_ordL R ≤ 1 := by
      rcases hR' with rfl | ⟨ℓ, ch', rfl, hk, -⟩
      · simp [psteps_ordL]
      · simp [psteps_ordL, hk, Kind.ord]
    have h3 : psteps_ordL [sx, la] = 3 := by simp [psteps_ordL, hsx, la, mkC, Kind.ord]
    rw [h3]; linarith
  · intro heq hlt
    have h3 : psteps_ordL [sx, la] = 3 := by simp [psteps_ordL, hsx, la, mkC, Kind.ord]
    rcases hR' with rfl | ⟨ℓ, ch', rfl, hk, hx⟩
    · rw [h3] at heq; simp [psteps_ordL] at heq
    · have hαx : ¬ g₁.SameBlock (newA 0) (liftA 1 x) := fun h =>
        liftA_ne_newA 1 x 0 ((hlt.blkNew _).1 h)
      have hℓl : ℓ.label.isSome = true := by rw [hRl ℓ (by simp)]; rfl
      refine ⟨?_, Or.inl ?_⟩
      · rw [List.map_cons, List.map_cons, List.map_nil, List.sum_cons, List.sum_cons, List.sum_nil,
          wBP_none rfl, wBP_L (B := fun u => g₁.SameBlock u (liftA 1 x)) (a := la) rfl rfl,
          if_neg hαx]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [wBP_L hk hℓl, if_pos (by rw [hx]; exact Graph.sameBlock_refl _ _)]
        norm_num
      · simp [hsx, la, mkC, Kind.isSolid]

end RoundL

section RoundL2

variable {k n : ℕ}

theorem mem_oWeightP2Pos {x : Atom k n} {h : Graph k n} {E : TExpansion k n}
    (hE : oWeightP2Pos x h = some E) {s : Tracked k n} (hs : s ∈ E) :
    ∃ i, ∃ hi : i < h.comps.length, h.comps[i].kind = .light .plus ∧ h.comps[i].x = x ∧
      ∃ cs co, s = ⟨n + 1, ⟨cs, co⟩, liftA 1⟩ ∧
        (cs = liftCs 1 (h.comps.eraseIdx i) ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
            mkC (.light .plus) (newA 0) (newA 0)] ∨
         cs = liftCs 1 h.comps ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
            mkC (.light .plus) (newA 0) (newA 0)] ∨
         ∃ j, ∃ hj : j < (h.comps.eraseIdx i).length, ∃ ps,
           (((h.comps.eraseIdx i)[j]).map (liftA 1)).dPieces (newA 0) (liftA 1 x) = some ps ∧
           cs = liftCs 1 ((h.comps.eraseIdx i).eraseIdx j) ++ ps ++
             [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 x)]) := by
  unfold oWeightP2Pos at hE
  split at hE
  · cases hE
  · rename_i i hi
    obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
    simp only [Option.some.injEq] at hE
    subst hE
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    refine ⟨i, hlt, hp.1, hp.2, ?_⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_map] at hs
    rcases hs with rfl | rfl | ⟨d, hd, rfl⟩
    · exact ⟨_, _, rfl, Or.inl rfl⟩
    · exact ⟨_, _, rfl, Or.inr (Or.inl rfl)⟩
    · obtain ⟨j, hj, ps, hps, rfl⟩ := psteps_mem_dTerms.1 hd
      have hj' : j < (h.comps.eraseIdx i).length := by simpa [liftCs] using hj
      refine ⟨_, _, rfl, Or.inr (Or.inr ⟨j, hj', ps, ?_, ?_⟩)⟩
      · rw [← hps]; simp [liftCs]
      · simp [liftCs, List.eraseIdx_map]

end RoundL2

/-! ## Complex conjugation of components -/

section ConjC

/-- The complex conjugate of a component. -/
def conjC {V : Type*} (c : Comp V) : Comp V := { c with kind := c.kind.conj }

theorem Kind.conj_conj' (κ : Kind) : κ.conj.conj = κ := by
  cases κ with
  | G ch => cases ch <;> rfl
  | weight ch => cases ch <;> rfl
  | light ch => cases ch <;> rfl
  | inv ch => cases ch <;> rfl
  | wD ch d => cases ch <;> rfl
  | waved w => cases w <;> rfl
  | _ => rfl

theorem conjC_conjC {V : Type*} (c : Comp V) : conjC (conjC c) = c := by
  rcases c with ⟨κ, a, b, mi, l⟩
  simp [conjC, Kind.conj_conj']

theorem map_conjC_conjC {V : Type*} (L : List (Comp V)) :
    (L.map conjC).map conjC = L := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id L]
  exact List.map_congr_left fun c _ => conjC_conjC c

theorem conjC_map {V W : Type*} (f : V → W) (c : Comp V) :
    conjC (c.map f) = (conjC c).map f := rfl

theorem solidC_conj {V : Type*} [DecidableEq V] (ch : Charge) (u v : V) :
    conjC (solidC ch u v) = solidC ch.flip u v := by
  unfold solidC
  split_ifs <;> cases ch <;> rfl

theorem conjC_mk {V : Type*} (κ : Kind) (a b : V) (mi : List V) (l : Option (PQ × V)) :
    conjC (⟨κ, a, b, mi, l⟩ : Comp V) = ⟨κ.conj, a, b, mi, l⟩ := rfl

theorem dPieces_conj {V : Type*} [DecidableEq V] (p q : V) (c : Comp V) :
    ((conjC c).dPieces p q).map (List.map conjC) = c.dPieces q p := by
  rcases c with ⟨κ, a, b, mi, l⟩
  rw [conjC_mk]
  cases κ with
  | G ch => cases ch <;> simp [Comp.dPieces, Kind.conj, Kind.isWeight, solidC_conj, Charge.flip]
  | weight ch => cases ch <;> simp [Comp.dPieces, Kind.conj, Kind.isWeight, solidC_conj,
      Charge.flip]
  | light ch => cases ch <;> simp [Comp.dPieces, Kind.conj, Kind.isWeight, solidC_conj,
      Charge.flip]
  | waved w => cases w <;> simp [Comp.dPieces, Kind.conj]
  | _ => simp [Comp.dPieces, Kind.conj]

private theorem conjC_mkC {V : Type*} (κ : Kind) (u v : V) : conjC (mkC κ u v) = mkC κ.conj u v :=
  rfl

theorem Graph.conj_comps' {k n : ℕ} (g : Graph k n) : g.conj.comps = g.comps.map conjC :=
  rfl

private theorem Graph.conj_coeff' {k n : ℕ} (g : Graph k n) : g.conj.coeff = Coeff.conj g.coeff :=
  rfl

theorem mem_TExpansion_conj {k n : ℕ} {E : TExpansion k n} {s : Tracked k n} :
    s ∈ E.conj ↔ ∃ s₀ ∈ E, s = ⟨s₀.nOut, s₀.g.conj, s₀.f⟩ := by
  unfold TExpansion.conj
  rw [List.mem_map]
  constructor
  · rintro ⟨s₀, hs, rfl⟩; exact ⟨s₀, hs, rfl⟩
  · rintro ⟨s₀, hs, rfl⟩; exact ⟨s₀, hs, rfl⟩

end ConjC

section RoundL3

variable {k n : ℕ}

/-- A term of an identity applied to `Γ.pCore`, read inside `P_x`: the removed components `R₀`
and the added components `A₀`. -/
theorem liftOut {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hlr : g.LabRand)
    {R₀ B : List (Comp (Atom k n))} (hB : g.pCore.comps.Perm (R₀ ++ B))
    (A₀ : List (Comp (Atom k (n + 1)))) :
    g.comps.Perm (R₀.map (rl x) ++ (B.map (rl x) ++ g.pEnv)) ∧
    ((liftCs 1 B ++ A₀).map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1))).Perm
      ((B.map (rl x) ++ g.pEnv).map (Comp.map (liftA 1)) ++ A₀.map (rl (liftA 1 x))) := by
  constructor
  · refine (comps_perm_core g).trans ?_
    rw [← relab_pCore hlab hlr, ← List.append_assoc, ← List.map_append]
    exact (hB.map _).append_right _
  · have : (rl (liftA 1 x) ∘ Comp.map (liftA 1)) = (Comp.map (liftA 1) ∘ rl x) := by
      funext c; simp only [Function.comp_apply]; exact rl_map (liftA 1) x c
    simp only [liftCs, List.map_append, List.map_map, this, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm

theorem rl_core {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hlr : g.LabRand)
    {c₀ : Comp (Atom k n)} (hc : c₀ ∈ g.pCore.comps) (hr : c₀.kind.isRandom = true) :
    rl x c₀ ∈ g.comps ∧ (rl x c₀).label = some (.P, x) ∧ (rl x c₀).kind = c₀.kind ∧
      (rl x c₀).x = c₀.x ∧ (rl x c₀).y = c₀.y := by
  refine ⟨?_, by simp [rl, hr], by simp [rl, hr], by simp [rl, hr], by simp [rl, hr]⟩
  have : rl x c₀ ∈ g.pCore.comps.map (rl x) := List.mem_map_of_mem hc
  rw [relab_pCore hlab hlr] at this
  exact (List.mem_filter.1 this).1

theorem dPieces_rl {V W : Type*} [DecidableEq W] (y : V) (f : V → W) (c : Comp V)
    (p q : W) : ((rl y c).map f).dPieces p q = (c.map f).dPieces p q := by
  unfold rl; split_ifs <;> rfl

theorem dPieces_random {V : Type*} [DecidableEq V] {p q : V} {c : Comp V}
    {ps : List (Comp V)} (h : c.dPieces p q = some ps) : c.kind.isRandom = true := by
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ with
  | G ch => rfl
  | weight ch => rfl
  | light ch => rfl
  | _ => simp [Comp.dPieces] at h

theorem liftCs_conj (L : List (Comp (Atom k n))) :
    (liftCs 1 L).map conjC = liftCs 1 (L.map conjC) := by
  simp only [liftCs, List.map_map]
  rfl

/-- The terms of [II, (4.23)] inside `P_x` at a light weight with label `P_x` on `x`. -/
theorem termsL {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    (hLx : ∃ c ∈ g.comps, (∃ ch, c.kind = .light ch) ∧ c.x = x ∧ c.label = some (.P, x)) :
    ∀ t ∈ oWeightP2T x g, PStepsTermOK (C + 5) x g t := by
  have hN := hS.nn
  have hlab := hN.lab
  have hlr := hN.plain.labRand
  have hP : g.IsPFormAt x := by
    obtain ⟨c, hc, -, -, hl⟩ := hLx; exact ⟨⟨c, hc, hl⟩, hN.lab⟩
  have hsxrl : rl (liftA 1 x) (mkC (.waved .s) (liftA 1 x) (newA 0)) =
      mkC (.waved .s) (liftA 1 x) (newA 0) := by simp [rl, mkC, Kind.isRandom]
  -- the term shapes
  have keyA : ∀ (ℓ₀ : Comp (Atom k n)) (B : List (Comp (Atom k n))) (ch : Charge),
      g.pCore.comps.Perm ([ℓ₀] ++ B) → ℓ₀.kind = .light ch → ℓ₀.x = x →
      ∀ co (g₁ : Graph k (n + 1)), g₁ = ⟨(liftCs 1 B ++ [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light ch) (newA 0) (newA 0)]).map
        (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), co⟩ →
      Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩ →
      PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
    intro ℓ₀ B ch hB hk hx co g₁ hg₁ hch
    obtain ⟨hR, hL⟩ := liftOut hlab hlr hB [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light ch) (newA 0) (newA 0)]
    have hc := rl_core hlab hlr (hB.symm.subset (List.mem_append_left _ (List.mem_singleton_self _)))
      (by rw [hk]; rfl)
    have hL' : g₁.comps.Perm (((B.map (rl x) ++ g.pEnv)).map (Comp.map (liftA 1)) ++
        [mkC (.waved .s) (liftA 1 x) (newA 0), rl (liftA 1 x) (mkC (.light ch) (newA 0) (newA 0))]) := by
      rw [hg₁]; simpa only [List.map_cons, List.map_nil, hsxrl] using hL
    refine termLa hS hR ?_ (Or.inr ⟨_, ch, rfl, by rw [hc.2.2.1, hk], by rw [hc.2.2.2.1, hx]⟩)
      hL' hch
    intro c hc'
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc'
    rw [hc']; exact hc.2.1
  have keyB : ∀ (ch : Charge) co (g₁ : Graph k (n + 1)),
      g₁ = ⟨(liftCs 1 g.pCore.comps ++ [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light ch) (newA 0) (newA 0)]).map
        (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), co⟩ →
      Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩ →
      PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
    intro ch co g₁ hg₁ hch
    have hB : g.pCore.comps.Perm ([] ++ g.pCore.comps) := by simp
    obtain ⟨hR, hL⟩ := liftOut hlab hlr hB [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light ch) (newA 0) (newA 0)]
    have hL' : g₁.comps.Perm (((g.pCore.comps.map (rl x) ++ g.pEnv)).map (Comp.map (liftA 1)) ++
        [mkC (.waved .s) (liftA 1 x) (newA 0), rl (liftA 1 x) (mkC (.light ch) (newA 0) (newA 0))]) := by
      rw [hg₁]; simpa only [List.map_cons, List.map_nil, hsxrl] using hL
    exact termLa hS hR (by simp) (Or.inl (by simp)) hL' hch
  have keyC : ∀ (ℓ₀ c₀ : Comp (Atom k n)) (B : List (Comp (Atom k n))) (ch : Charge),
      g.pCore.comps.Perm ([ℓ₀, c₀] ++ B) → ℓ₀.kind = .light ch → ℓ₀.x = x →
      ∀ p q : Atom k (n + 1), ((p = newA 0 ∧ q = liftA 1 x) ∨ (p = liftA 1 x ∧ q = newA 0)) →
      ∀ ps, (c₀.map (liftA 1)).dPieces p q = some ps →
      ∀ co (g₁ : Graph k (n + 1)), g₁ = ⟨(liftCs 1 B ++ (ps ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.G ch) (newA 0) (liftA 1 x)])).map (rl (liftA 1 x)) ++
          g.pEnv.map (Comp.map (liftA 1)), co⟩ →
      Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩ →
      PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
    intro ℓ₀ c₀ B ch hB hk hx p q hpq ps hps co g₁ hg₁ hch
    obtain ⟨hR, hL⟩ := liftOut hlab hlr hB (ps ++ [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G ch) (newA 0) (liftA 1 x)])
    have hℓ := rl_core hlab hlr (hB.symm.subset (List.mem_append_left B (by simp : ℓ₀ ∈ [ℓ₀, c₀])))
      (by rw [hk]; rfl)
    have hc := rl_core hlab hlr (hB.symm.subset (List.mem_append_left B (by simp : c₀ ∈ [ℓ₀, c₀])))
      (by have := dPieces_random hps; simpa [Comp.map] using this)
    simp only [List.map_cons, List.map_nil] at hR
    have hL' : g₁.comps.Perm (((B.map (rl x) ++ g.pEnv)).map (Comp.map (liftA 1)) ++
        (ps ++ [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G ch) (newA 0) (liftA 1 x)]).map
          (rl (liftA 1 x))) := by rw [hg₁]; exact hL
    refine termD hS hR hℓ.2.1 hc.2.1 (Or.inl rfl) (ch := ch)
      (Or.inl ⟨by rw [hℓ.2.2.1, hk], by rw [hℓ.2.2.2.1, hx], rfl⟩)
      (fun _ _ => ⟨rfl, by rw [hℓ.2.2.1, hk]; rfl⟩) hpq (by rw [dPieces_rl]; exact hps)
      (e₀ := mkC (.G ch) (newA 0) (liftA 1 x)) (Or.inl ⟨rfl, rfl⟩) ?_ hL' hch
    simp [solidC, mkC, Ne.symm (liftA_ne_newA 1 x 0)]
  intro t ht
  have hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨t.nOut, t.g⟩ :=
    .single (QElemStep.pWeight2 x g t hP hN.plain ht)
  unfold oWeightP2T at ht
  rcases hE : oWeightP2Pos x g.pCore with _ | E
  · rw [hE] at ht
    dsimp only at ht
    rcases hE' : oWeightP2Pos x g.pCore.conj with _ | E
    · exfalso
      have hn1 : g.pCore.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) = none := by
        unfold oWeightP2Pos at hE
        split at hE
        · assumption
        · cases hE
      have hn2 : g.pCore.conj.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) =
          none := by
        unfold oWeightP2Pos at hE'
        split at hE'
        · assumption
        · cases hE'
      obtain ⟨c, hc, ⟨ch, hk⟩, hx, hl⟩ := hLx
      have hc₀ : { c with label := none } ∈ g.pCore.comps := by
        rw [pCore_comps]
        exact List.mem_map_of_mem (List.mem_filter.2 ⟨hc, by simp [coreP, hl]⟩)
      cases ch
      · have := List.findIdx?_eq_none_iff.1 hn1 _ hc₀
        simp [hk, hx] at this
      · have := List.findIdx?_eq_none_iff.1 hn2 (conjC { c with label := none })
          (by rw [Graph.conj_comps']; exact List.mem_map_of_mem hc₀)
        simp [conjC, hk, hx, Kind.conj, Charge.flip] at this
    · rw [hE'] at ht
      dsimp only at ht
      obtain ⟨s', hs', -, rfl⟩ := mem_pLiftT.1 ht
      obtain ⟨s, hs, rfl⟩ := mem_TExpansion_conj.1 hs'
      obtain ⟨i, hi, hk, hx, cs, co, rfl, hcs⟩ := mem_oWeightP2Pos hE' hs
      have hcore : g.pCore.conj.comps.map conjC = g.pCore.comps := by
        rw [Graph.conj_comps', map_conjC_conjC]
      have hk' : (conjC g.pCore.conj.comps[i]).kind = .light .minus := by
        simp only [conjC, hk]; rfl
      have hx' : (conjC g.pCore.conj.comps[i]).x = x := hx
      have hpermi : g.pCore.comps.Perm ([conjC g.pCore.conj.comps[i]] ++
          (g.pCore.conj.comps.eraseIdx i).map conjC) := by
        have := (List.getElem_cons_eraseIdx_perm hi).symm.map conjC
        rw [hcore] at this
        simpa only [List.map_cons, List.singleton_append] using this
      rcases hcs with rfl | rfl | ⟨j, hj, ps, hps, rfl⟩
      · refine keyA _ ((g.pCore.conj.comps.eraseIdx i).map conjC) .minus hpermi hk' hx' co.conj _
          ?_ hch
        simp only [Graph.conj_comps', Graph.conj_coeff', List.map_append, liftCs_conj, List.map_cons, List.map_nil,
          conjC_mkC, Kind.conj, Charge.flip]
      · refine keyB .minus co.conj _ ?_ hch
        simp only [Graph.conj_comps', Graph.conj_coeff', List.map_append, liftCs_conj, List.map_cons, List.map_nil,
          conjC_mkC, Kind.conj, Charge.flip, map_conjC_conjC]
      · have hB : g.pCore.comps.Perm ([conjC g.pCore.conj.comps[i],
            conjC (g.pCore.conj.comps.eraseIdx i)[j]] ++
            ((g.pCore.conj.comps.eraseIdx i).eraseIdx j).map conjC) := by
          have := ((List.getElem_cons_eraseIdx_perm hi).symm.trans
            (List.Perm.cons _ (List.getElem_cons_eraseIdx_perm hj).symm)).map conjC
          rw [hcore] at this
          simpa only [List.map_cons, List.cons_append, List.nil_append] using this
        have hps' : ((conjC (g.pCore.conj.comps.eraseIdx i)[j]).map (liftA 1)).dPieces
            (liftA 1 x) (newA 0) = some (ps.map conjC) := by
          rw [← dPieces_conj, conjC_map, conjC_conjC, hps]
          rfl
        refine keyC _ _ _ .minus hB hk' hx' _ _ (Or.inr ⟨rfl, rfl⟩) _ hps' co.conj _ ?_ hch
        simp only [Graph.conj_comps', Graph.conj_coeff', List.map_append, liftCs_conj, List.map_cons, List.map_nil,
          conjC_mkC, Kind.conj, Charge.flip, List.append_assoc]
  · rw [hE] at ht
    dsimp only at ht
    obtain ⟨s, hs, -, rfl⟩ := mem_pLiftT.1 ht
    obtain ⟨i, hi, hk, hx, cs, co, rfl, hcs⟩ := mem_oWeightP2Pos hE hs
    rcases hcs with rfl | rfl | ⟨j, hj, ps, hps, rfl⟩
    · exact keyA _ _ .plus (List.getElem_cons_eraseIdx_perm hi).symm hk hx co _ rfl hch
    · exact keyB .plus co _ rfl hch
    · have hB : g.pCore.comps.Perm ([g.pCore.comps[i], (g.pCore.comps.eraseIdx i)[j]] ++
          (g.pCore.comps.eraseIdx i).eraseIdx j) :=
        (List.getElem_cons_eraseIdx_perm hi).symm.trans
          (List.Perm.cons _ (List.getElem_cons_eraseIdx_perm hj).symm)
      exact keyC _ _ _ .plus hB hk hx _ _ (Or.inl ⟨rfl, rfl⟩) ps hps co _
        (by simp only [List.append_assoc]) hch

end RoundL3

/-! ## Terms with one new atom read inside `P_x`: values -/

section PLiftVal

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ}

theorem pv_map' {V W : Type*} (D₀ : Data ι) (σ : W → ι) (f : V → W)
    (cs : List (Comp V)) : pv D₀ σ (cs.map (Comp.map f)) = pv D₀ (σ ∘ f) cs := by
  rw [pv_eq, pv_eq, rv_map, dv_map]

/-- A term with one new atom read inside `P_x`: the factors of `Γ_ω`, and the sum over the label
of the new atom. -/
theorem T1_plift (x : Atom k n) (g : Graph k n) (cs : List (Comp (Atom k (n + 1))))
    (d : Coeff) (hcs : Unl cs) (e : Fin k → ι) (ω : Ω) (s : Fin n → ι) :
    T1 PF D e ω ⟨cs.map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), d⟩ s =
      pv (D ω) (Sum.elim e s) g.pEnv * ∑ α, d.eval (msc A.z) *
        dv (D ω) (Sum.elim e (Fin.append s ![α])) cs *
        PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e (Fin.append s ![α])) cs) ω := by
  unfold T1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [termR_lifted A (liftA 1 x) cs _ d hcs (fun c hc => ?_) _ ω, pv_map',
    elim_append_comp_liftA, elim_append_liftA, m_eq A]
  · ring
  · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    simp [Comp.map, pEnv_unl g c' hc']

theorem pLiftT_cons_t1 (x : Atom k n) (g : Graph k n) (cs : List (Comp (Atom k (n + 1))))
    (d : Coeff) (hcs : Unl cs) (E : TExpansion k n) :
    pLiftT x g (PS_t1 cs d :: E) =
      PS_t1 (cs.map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1))) d :: pLiftT x g E := by
  unfold pLiftT
  rw [List.filterMap_cons, if_neg]
  · rfl
  · simp only [PS_t1, List.any_eq_true, decide_eq_true_eq, not_exists, not_and]
    intro c hc
    rw [hcs c hc]
    simp

theorem pLiftT_map_t1 (x : Atom k n) (g : Graph k n) {β : Type*} (l : List β)
    (G : β → List (Comp (Atom k (n + 1)))) (d : β → Coeff) (hG : ∀ j ∈ l, Unl (G j)) :
    pLiftT x g (l.map fun j => PS_t1 (G j) (d j)) =
      l.map fun j => PS_t1 ((G j).map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1))) (d j) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.map_cons, pLiftT_cons_t1 x g _ _ (hG j (by simp)),
      ih fun j' hj' => hG j' (List.mem_cons_of_mem _ hj')]
    rfl

theorem pLiftT_nil (x : Atom k n) (g : Graph k n) : pLiftT x g [] = [] := rfl

theorem pLiftT_append (x : Atom k n) (g : Graph k n) (E₁ E₂ : TExpansion k n) :
    pLiftT x g (E₁ ++ E₂) = pLiftT x g E₁ ++ pLiftT x g E₂ := by
  unfold pLiftT
  rw [List.filterMap_append]

theorem good_of_test {f : Ω → ℂ} (h : A.Test f) : A.Good f := A.test_good f h

/-- [II, (4.23)] with `P_x` distributed over the sums. -/
theorem weightP_lin (X : ι) (F : Ω → ℂ) (hF : A.Test F) (ω : Ω) :
    PF.P X (fun ω' => (A.G ω' X X - msc A.z) * F ω') ω =
      ∑ α, msc A.z ^ 2 * (A.S X α : ℂ) * PF.P X (fun ω' => (A.G ω' α α - msc A.z) * F ω') ω +
      ∑ α, msc A.z * (A.S X α : ℂ) *
        PF.P X (fun ω' => (A.G ω' α α - msc A.z) * (A.G ω' X X - msc A.z) * F ω') ω -
      ∑ α, msc A.z * (A.S X α : ℂ) *
        PF.P X (fun ω' => A.G ω' α X * A.dh α X F ω') ω := by
  have h := congrFun (weightP Ω ι PF D A X F hF) ω
  simp only [Pi.sub_apply] at h
  rw [h]
  have tG : ∀ a b, A.Test fun ω => A.G ω a b := test_G A
  have PS_t1' : ∀ α, A.Test fun ω' => (A.G ω' α α - msc A.z) * F ω' :=
    fun α => test_mul' A (test_sub' A (tG _ _) (test_const' A _)) hF
  have t2' : ∀ α, A.Test fun ω' => (A.G ω' α α - msc A.z) * (A.G ω' X X - msc A.z) * F ω' :=
    fun α => test_mul' A (test_mul' A (test_sub' A (tG _ _) (test_const' A _))
      (test_sub' A (tG _ _) (test_const' A _))) hF
  have t3' : ∀ α, A.Test fun ω' => A.G ω' α X * A.dh α X F ω' :=
    fun α => test_mul' A (tG _ _) (test_dh' A _ _ hF)
  rw [P_congr' (f := fun ω => msc A.z ^ 2 * ∑ α, (A.S X α : ℂ) * (A.G ω α α - msc A.z) * F ω +
      msc A.z * ∑ α, (A.S X α : ℂ) * (A.G ω α α - msc A.z) * (A.G ω X X - msc A.z) * F ω)
    (g := fun ω => (∑ α, msc A.z ^ 2 * (A.S X α : ℂ) * ((A.G ω α α - msc A.z) * F ω)) +
      ∑ α, msc A.z * (A.S X α : ℂ) * ((A.G ω α α - msc A.z) * (A.G ω X X - msc A.z) * F ω))
    (fun ω => by simp only [Finset.mul_sum]; congr 1 <;>
      exact Finset.sum_congr rfl fun α _ => by ring)]
  rw [P_congr' (f := fun ω => msc A.z * ∑ α, (A.S X α : ℂ) * A.G ω α X * A.dh α X F ω)
    (g := fun ω => ∑ α, msc A.z * (A.S X α : ℂ) * (A.G ω α X * A.dh α X F ω))
    (fun ω => by simp only [Finset.mul_sum]; exact Finset.sum_congr rfl fun α _ => by ring)]
  have g1 : ∀ α, A.Good fun ω => msc A.z ^ 2 * (A.S X α : ℂ) * ((A.G ω α α - msc A.z) * F ω) :=
    fun α => good_of_test A (test_mul' A (test_const' A _) (PS_t1' α))
  have g2 : ∀ α, A.Good fun ω => msc A.z * (A.S X α : ℂ) *
      ((A.G ω α α - msc A.z) * (A.G ω X X - msc A.z) * F ω) :=
    fun α => good_of_test A (test_mul' A (test_const' A _) (t2' α))
  have g3 : ∀ α, A.Good fun ω => msc A.z * (A.S X α : ℂ) * (A.G ω α X * A.dh α X F ω) :=
    fun α => good_of_test A (test_mul' A (test_const' A _) (t3' α))
  rw [P_add' A (good_sum' A _ g1) (good_sum' A _ g2), P_sum' A _ g1, P_sum' A _ g2, P_sum' A _ g3]
  simp only [P_cmul' A _ (good_of_test A (PS_t1' _)), P_cmul' A _ (good_of_test A (t2' _)),
    P_cmul' A _ (good_of_test A (t3' _))]

end PLiftVal

/-! ## The value of [II, (4.23)] inside `P_x` -/

theorem dTerms_unl {V : Type*} [DecidableEq V] {p q : V} {cs : List (Comp V)}
    (h : ∀ c ∈ cs, c.label = none) : ∀ d ∈ dTerms p q cs, ∀ c ∈ d, c.label = none := by
  intro d hd c hc
  obtain ⟨j, hj, ps, hps, rfl⟩ := psteps_mem_dTerms.1 hd
  rcases List.mem_append.1 hc with h' | h'
  · exact h c (List.mem_of_mem_eraseIdx h')
  · have key : ∀ (ch : Charge) (u v : V), (solidC ch u v).label = none := by
      intro ch u v; unfold solidC; split_ifs <;> rfl
    rcases hk : cs[j] with ⟨κ, a, b, mi, l⟩
    rw [hk] at hps
    cases κ with
    | G ch => cases ch <;> simp [Comp.dPieces] at hps <;> subst hps <;> simp at h' <;>
        rcases h' with rfl | rfl <;> exact key _ _ _
    | weight ch => cases ch <;> simp [Comp.dPieces] at hps <;> subst hps <;> simp at h' <;>
        rcases h' with rfl | rfl <;> exact key _ _ _
    | light ch => cases ch <;> simp [Comp.dPieces] at hps <;> subst hps <;> simp at h' <;>
        rcases h' with rfl | rfl <;> exact key _ _ _
    | _ => simp [Comp.dPieces] at hps

section ValueL

variable {k n : ℕ}

theorem core_lift_bas {g : Graph k n} (hp : g.Plain) (L : List (Comp (Atom k n)))
    (hL : ∀ c ∈ L, c ∈ g.pCore.comps) :
    ∀ c ∈ liftCs 1 L, basB c = true ∧ c.label = none := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  refine ⟨by rw [basB_map]; exact pCore_basB hp c' (hL c' hc'), ?_⟩
  simp [Comp.map, pCore_unl g c' (hL c' hc')]

/-- The value of [II, (4.23)] at the first light weight of positive charge on `x` of `𝒢`, inside
`P_x`. -/
theorem valueL_plain {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hp : g.Plain)
    {E : TExpansion k n} (hE : oWeightP2Pos x g.pCore = some E) :
    TExpansion.ValueEq (pLiftT x g E) g modelAdm := by
  intro Ω ι _ _ PF D hA e
  obtain ⟨A⟩ := hA
  funext ω
  unfold oWeightP2Pos at hE
  split at hE
  · cases hE
  rename_i i hi
  obtain ⟨hlt, hpi, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
  simp only [Bool.and_eq_true, beq_iff_eq] at hpi
  simp only [Option.some.injEq] at hE
  subst hE
  set core := g.pCore.comps with hcore
  set core' := core.eraseIdx i with hcore'
  have hsub' : ∀ c ∈ core', c ∈ g.pCore.comps := fun c hc => List.mem_of_mem_eraseIdx hc
  have hbF := core_lift_bas hp core' hsub'
  have hU1 : Unl (liftCs 1 core' ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.light .plus) (newA 0) (newA 0)]) :=
    Unl_append.2 ⟨fun c hc => (hbF c hc).2, by simp [Unl, mkC]⟩
  have hU2 : Unl (liftCs 1 core ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.light .plus) (newA 0) (newA 0)]) :=
    Unl_append.2 ⟨fun c hc => (core_lift_bas hp core (fun c hc => hc) c hc).2,
      by simp [Unl, mkC]⟩
  have hspec := fun (σ : Atom k (n + 1) → ι) =>
    dTerms_spec A σ (newA 0) (liftA 1 x) (liftCs 1 core') hbF
  have hU3 : ∀ d ∈ dTerms (newA 0) (liftA 1 x) (liftCs 1 core'),
      Unl (d ++ [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 x)]) :=
    fun d hd => Unl_append.2 ⟨dTerms_unl (fun c hc => (hbF c hc).2) d hd, by simp [Unl, mkC]⟩
  change S PF D e ω (pLiftT x g ([PS_t1 (liftCs 1 core' ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.light .plus) (newA 0) (newA 0)]) (cm * cm * g.coeff),
    PS_t1 (liftCs 1 core ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.light .plus) (newA 0) (newA 0)]) (cm * g.coeff)] ++
    (dTerms (newA 0) (liftA 1 x) (liftCs 1 core')).map fun d =>
      PS_t1 (d ++ [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 x)])
        (cm * g.coeff))) = g.valR PF D e ω
  rw [pLiftT_append, pLiftT_cons_t1 x g _ _ hU1, pLiftT_cons_t1 x g _ _ hU2,
    pLiftT_map_t1 x g _ _ _ hU3]
  simp only [List.cons_append, List.nil_append, List.singleton_append]
  rw [S_cons_t1, S_cons_t1, pLiftT_nil, List.nil_append, S_map_t1, valR_T0,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [T1_plift A x g _ _ hU1, T1_plift A x g _ _ hU2]
  rw [List.map_congr_left fun d hd => T1_plift A x g _ _ (hU3 d hd) e ω s]
  rw [T0, termR_pform A hlab hp.labRand, m_eq A]
  -- the core and its parts
  have hci : core[i].kind = .light .plus ∧ core[i].x = x := hpi
  have hperm : core.Perm (core[i] :: core') := (List.getElem_cons_eraseIdx_perm hlt).symm
  have hrcore : ∀ ω', rv (D ω') (Sum.elim e s) core =
      (A.G ω' (Sum.elim e s x) (Sum.elim e s x) - msc A.z) * rv (D ω') (Sum.elim e s) core' := by
    intro ω'
    have : rv (D ω') (Sum.elim e s) core = rv (D ω') (Sum.elim e s) (core[i] :: core') := by
      unfold rv; exact (List.Perm.prod_eq ((hperm.filter _).map _))
    rw [this, rv_cons]
    have hck : core[i] = mkC (.light .plus) x x := by
      have hmem : core[i] ∈ g.pCore.comps := List.getElem_mem hlt
      obtain ⟨d, hd, -, hdc⟩ := pCore_mem hmem
      have hwf := (hp d hd).2.2.2.2.1
      have hdk : d.kind = .light .plus := by rw [← hci.1, hdc]
      have hdx : d.x = x := by rw [← hci.2, hdc]
      have hdy : d.y = x := by rw [hwf (by rw [hdk]; rfl), hdx]
      have hdm : d.minor = [] := (hp d hd).1
      rw [hdc]
      rcases d with ⟨κ, a, b, mi, l⟩
      simp only at hdk hdx hdy hdm
      subst hdk hdx hdy hdm
      rfl
    rw [hck]
    simp [val_light A, Charge.apply, Kind.isRandom]
  have hdcore : dv (D ω) (Sum.elim e s) core = dv (D ω) (Sum.elim e s) core' := by
    have : dv (D ω) (Sum.elim e s) core = dv (D ω) (Sum.elim e s) (core[i] :: core') := by
      unfold dv; exact (List.Perm.prod_eq ((hperm.filter _).map _))
    rw [this, dv_cons, hci.1]
    simp [Kind.isRandom]
  set F : Ω → ℂ := fun ω' => rv (D ω') (Sum.elim e s) core' with hF
  have hFt : A.Test F := rv_test A _ core' fun c hc => pCore_basB hp c (hsub' c hc)
  have hσα : ∀ α : ι, Sum.elim e (Fin.append s ![α]) ∘ liftA 1 = Sum.elim e s := fun α =>
    elim_append_comp_liftA e s ![α]
  -- the first two terms
  have h1 : ∀ α, dv (D ω) (Sum.elim e (Fin.append s ![α])) (liftCs 1 core' ++
      [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light .plus) (newA 0) (newA 0)]) =
      dv (D ω) (Sum.elim e s) core' * (A.S (Sum.elim e s x) α : ℂ) := by
    intro α
    simp [dv_liftCs, hσα, Kind.isRandom, val_s A]
  have h1r : ∀ α ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (liftCs 1 core' ++
      [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light .plus) (newA 0) (newA 0)]) =
      (A.G ω' α α - msc A.z) * F ω' := by
    intro α ω'
    simp [rv_liftCs, hσα, Kind.isRandom, val_light A, Charge.apply, hF]
    ring
  have h2 : ∀ α, dv (D ω) (Sum.elim e (Fin.append s ![α])) (liftCs 1 core ++
      [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light .plus) (newA 0) (newA 0)]) =
      dv (D ω) (Sum.elim e s) core' * (A.S (Sum.elim e s x) α : ℂ) := by
    intro α
    simp [dv_liftCs, hσα, Kind.isRandom, val_s A, hdcore]
  have h2r : ∀ α ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (liftCs 1 core ++
      [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light .plus) (newA 0) (newA 0)]) =
      (A.G ω' α α - msc A.z) * (A.G ω' (Sum.elim e s x) (Sum.elim e s x) - msc A.z) * F ω' := by
    intro α ω'
    simp [rv_liftCs, hσα, Kind.isRandom, val_light A, Charge.apply, hrcore, hF]
    ring
  -- the derivative terms
  have hdd : ∀ α, ∀ d ∈ dTerms (newA 0) (liftA 1 x) (liftCs 1 core'),
      dv (D ω) (Sum.elim e (Fin.append s ![α])) (d ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.G .plus) (newA 0) (liftA 1 x)]) =
        dv (D ω) (Sum.elim e s) core' * (A.S (Sum.elim e s x) α : ℂ) := by
    intro α d hd
    have := ((hspec (Sum.elim e (Fin.append s ![α]))).1 d hd).2 (D ω)
    rw [dv_liftCs, hσα] at this
    simp [this, Kind.isRandom, val_s A]
  have hdr : ∀ α, ∀ ω', ((dTerms (newA 0) (liftA 1 x) (liftCs 1 core')).map fun d =>
      rv (D ω') (Sum.elim e (Fin.append s ![α])) (d ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.G .plus) (newA 0) (liftA 1 x)])).sum =
        -(A.G ω' α (Sum.elim e s x) * A.dh α (Sum.elim e s x) F ω') := by
    intro α ω'
    have := (hspec (Sum.elim e (Fin.append s ![α]))).2 ω'
    simp only [rv_liftCs, hσα, elim_append_newA, Matrix.cons_val_zero, elim_append_liftA] at this
    have hpt : ∀ d ∈ dTerms (newA 0) (liftA 1 x) (liftCs 1 core'),
        rv (D ω') (Sum.elim e (Fin.append s ![α])) (d ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
          mkC (.G .plus) (newA 0) (liftA 1 x)]) =
          rv (D ω') (Sum.elim e (Fin.append s ![α])) d * A.G ω' α (Sum.elim e s x) := by
      intro d _
      simp [Kind.isRandom, val_G A, Charge.apply]
    refine (congrArg List.sum (List.map_congr_left hpt)).trans ?_
    rw [List.sum_map_mul_right, this]
    ring
  have hgd : ∀ α, ∀ d ∈ dTerms (newA 0) (liftA 1 x) (liftCs 1 core'), A.Good fun ω' =>
      rv (D ω') (Sum.elim e (Fin.append s ![α])) (d ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.G .plus) (newA 0) (liftA 1 x)]) := by
    intro α d hd
    refine good_of_test A (rv_test A _ _ fun c hc => ?_)
    rcases List.mem_append.1 hc with h | h
    · exact (((hspec (Sum.elim e (Fin.append s ![α]))).1 d hd).1 c h).1
    · simp at h; rcases h with rfl | rfl <;> rfl
  have hD : ((dTerms (newA 0) (liftA 1 x) (liftCs 1 core')).map fun d =>
      pv (D ω) (Sum.elim e s) g.pEnv * ∑ α, (cm * g.coeff).eval (msc A.z) *
        dv (D ω) (Sum.elim e (Fin.append s ![α])) (d ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
          mkC (.G .plus) (newA 0) (liftA 1 x)]) *
        PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e (Fin.append s ![α])) (d ++
          [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 x)])) ω).sum =
      ∑ α, pv (D ω) (Sum.elim e s) g.pEnv * (msc A.z * g.coeff.eval (msc A.z) *
        (dv (D ω) (Sum.elim e s) core' * (A.S (Sum.elim e s x) α : ℂ)) *
        -PF.P (Sum.elim e s x) (fun ω' => A.G ω' α (Sum.elim e s x) *
          A.dh α (Sum.elim e s x) F ω') ω) := by
    rw [List.sum_map_mul_left, list_finset_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    congr 1
    rw [List.map_congr_left fun d hd => by rw [hdd α d hd]]
    rw [List.sum_map_mul_left, ← P_listSum' A _ (hgd α), P_congr' (hdr α),
      P_neg' A (good_of_test A (test_mul' A (test_G A _ _) (test_dh' A _ _ hFt))),
      ceval_mul, ceval_cm]
  rw [hD, hdcore, P_congr' hrcore]
  simp only [h1, h2, h1r, h2r, ceval_mul, ceval_cm]
  rw [weightP_lin A (Sum.elim e s x) F hFt ω]
  simp only [Finset.mul_sum, mul_add, mul_sub, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

end ValueL

/-! ## Complex conjugation of the identities inside `P_x` -/

section ConjValue

variable {k n : ℕ}

theorem Kind.conj_isRandom' (κ : Kind) : κ.conj.isRandom = κ.isRandom := by
  cases κ with
  | G ch => cases ch <;> rfl
  | weight ch => cases ch <;> rfl
  | light ch => cases ch <;> rfl
  | inv ch => cases ch <;> rfl
  | wD ch d => cases ch <;> rfl
  | waved w => cases w <;> rfl
  | _ => rfl

theorem rl_conjC {V : Type*} (y : V) (c : Comp V) : rl y (conjC c) = conjC (rl y c) := by
  unfold rl
  by_cases h : c.kind.isRandom = true
  · rw [if_pos (by simpa [conjC, Kind.conj_isRandom'] using h), if_pos h]; rfl
  · rw [if_neg (by simpa [conjC, Kind.conj_isRandom'] using h), if_neg h]

theorem pEnv_conj (g : Graph k n) : g.conj.pEnv = g.pEnv.map conjC := by
  unfold Graph.pEnv
  rw [Graph.conj_comps', List.filter_map]
  congr 1
  apply List.filter_congr
  intro c _
  simp [conjC, Kind.conj_isRandom']

theorem pLiftT_conj (x : Atom k n) (g : Graph k n) (E : TExpansion k n) :
    pLiftT x g E.conj = (pLiftT x g.conj E).conj := by
  unfold pLiftT TExpansion.conj
  rw [List.filterMap_map, List.map_filterMap]
  apply List.filterMap_congr
  intro t _
  simp only [Function.comp_apply, Graph.conj_comps', List.any_map]
  have hq : ((t.g.comps.map conjC).any fun c => decide (c.label = some (.Q, t.f x))) =
      (t.g.comps.any fun c => decide (c.label = some (.Q, t.f x))) := by
    rw [List.any_map]; rfl
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hq ▸ h1) h2
  · exact absurd (hq ▸ h2) h1
  · simp only [Option.map_some, Option.some.injEq]
    have e1 : (t.g.comps.map conjC).map (rl (t.f x)) =
        (t.g.comps.map (rl (t.f x))).map conjC := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun c _ => rl_conjC _ _
    have e2 : g.pEnv.map (Comp.map t.f) = ((g.pEnv.map conjC).map (Comp.map t.f)).map conjC := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun c _ => by
        simp only [Function.comp_apply, conjC_map, conjC_conjC]
    show (⟨t.nOut, ⟨(t.g.comps.map conjC).map (rl (t.f x)) ++ g.pEnv.map (Comp.map t.f),
      Coeff.conj t.g.coeff⟩, t.f⟩ : Tracked k n) = ⟨t.nOut, ⟨(t.g.comps.map (rl (t.f x)) ++
        g.conj.pEnv.map (Comp.map t.f)).map conjC, Coeff.conj t.g.coeff⟩, t.f⟩
    rw [e1, e2, pEnv_conj, ← List.map_append]

end ConjValue

section ConjValue2

variable {k n : ℕ}

/-- A formal sum with the value of `\overline{Γ}` gives, conjugated, a formal sum with the value
of `Γ`. -/
theorem valueEq_conj {g : Graph k n} {F : TExpansion k n}
    (hF : F.ValueEq g.conj modelAdm) (hokg : OK g.comps) (hokF : ∀ t ∈ F, OK t.g.comps) :
    F.conj.ValueEq g modelAdm := by
  intro Ω ι _ _ PF D hA e
  obtain ⟨A⟩ := hA
  funext ω
  have h1 := congrFun (hF Ω ι PF (fun ω => conjD (D ω)) ⟨conjAdm A⟩ e) ω
  have h2 := valR_conj (conjAdm A) g hokg e ω
  simp only [conjD_conjD] at h2
  simp only [TExpansion.conj, TExpansion.forget, Expansion.valR, List.map_map,
    Function.comp_def] at h1 ⊢
  rw [List.map_congr_left fun t ht => valR_conj A t.g (hokF t ht) e ω]
  have h3 : ((F.map fun t => star (t.g.valR PF (fun ω => conjD (D ω)) e ω)).sum) =
      star ((F.map fun t => t.g.valR PF (fun ω => conjD (D ω)) e ω).sum) := by
    rw [Complex.star_def, map_list_sum, List.map_map]
    rfl
  rw [h3, h1, h2]
  simp

end ConjValue2

/-! ## The value of [II, (4.23)] inside `P_x`, both charges -/

section ValueL2

variable {k n : ℕ}

theorem Kind.conj_isWeight' (κ : Kind) : κ.conj.isWeight = κ.isWeight := by
  cases κ with
  | G ch => cases ch <;> rfl
  | weight ch => cases ch <;> rfl
  | light ch => cases ch <;> rfl
  | inv ch => cases ch <;> rfl
  | wD ch d => cases ch <;> rfl
  | waved w => cases w <;> rfl
  | _ => rfl

theorem Kind.conj_inv' (κ : Kind) (ch : Charge) : κ.conj = .inv ch ↔ κ = .inv ch.flip := by
  cases κ with
  | inv c => cases c <;> cases ch <;> simp [Kind.conj, Charge.flip]
  | G c => cases c <;> simp [Kind.conj]
  | weight c => cases c <;> simp [Kind.conj]
  | light c => cases c <;> simp [Kind.conj]
  | wD c d => cases c <;> simp [Kind.conj]
  | waved w => cases w <;> simp [Kind.conj]
  | _ => simp [Kind.conj]

theorem Kind.conj_wD' (κ : Kind) (ch : Charge) (d : ℕ) :
    κ.conj = .wD ch d ↔ κ = .wD ch.flip d := by
  cases κ with
  | wD c d' => cases c <;> cases ch <;> simp [Kind.conj, Charge.flip]
  | G c => cases c <;> simp [Kind.conj]
  | weight c => cases c <;> simp [Kind.conj]
  | light c => cases c <;> simp [Kind.conj]
  | inv c => cases c <;> simp [Kind.conj]
  | waved w => cases w <;> simp [Kind.conj]
  | _ => simp [Kind.conj]

theorem Kind.conj_dot' (κ : Kind) : κ.conj = .dot ↔ κ = .dot := by
  cases κ with
  | G c => cases c <;> simp [Kind.conj]
  | weight c => cases c <;> simp [Kind.conj]
  | light c => cases c <;> simp [Kind.conj]
  | inv c => cases c <;> simp [Kind.conj]
  | wD c d => cases c <;> simp [Kind.conj]
  | waved w => cases w <;> simp [Kind.conj]
  | _ => simp [Kind.conj]

theorem Graph.Plain.conj {g : Graph k n} (hp : g.Plain) : g.conj.Plain := by
  intro c hc
  rw [Graph.conj_comps'] at hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp d hd
  refine ⟨h1, fun ch h => h2 ch.flip ((Kind.conj_inv' _ _).1 h),
    fun ch dd h => h3 ch.flip dd ((Kind.conj_wD' _ _ _).1 h),
    fun h => h4 ((Kind.conj_dot' _).1 h), ?_, ?_⟩
  · intro hw
    exact h5 (by simpa [conjC, Kind.conj_isWeight'] using hw)
  · intro hl
    simpa [conjC, Kind.conj_isRandom'] using h6 hl

theorem lab_conj {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) :
    ∀ c ∈ g.conj.comps, c.label = none ∨ c.label = some (.P, x) := by
  intro c hc
  rw [Graph.conj_comps'] at hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  exact hlab d hd

theorem pCore_conj (g : Graph k n) : g.conj.pCore = g.pCore.conj := by
  unfold Graph.pCore
  simp only [Graph.conj_comps', Graph.conj_coeff']
  congr 1
  rw [List.filter_map, List.map_map, List.map_map]
  rw [List.filter_congr (p := (fun c : Comp (Atom k n) => c.label.isSome || !c.kind.isRandom) ∘ conjC)
    (q := fun c => c.label.isSome || !c.kind.isRandom)
    (fun c _ => by simp [conjC, Kind.conj_isRandom'])]
  rfl

theorem okP {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hp : g.Plain) :
    OK g.comps := by
  intro c hc
  rcases hlab c hc with h | h
  · exact Or.inl h
  · refine Or.inr ⟨hp.labRand c hc (by rw [h]; rfl), ?_⟩
    obtain ⟨h1, h2, h3, -⟩ := hp c hc
    unfold basB
    rw [h1]
    cases hk : c.kind with
    | inv ch => exact absurd hk (h2 ch)
    | wD ch dd => exact absurd hk (h3 ch dd)
    | _ => rfl

theorem basB_solidC {V : Type*} [DecidableEq V] (ch : Charge) (u v : V) :
    basB (solidC ch u v) = true ∧ (solidC ch u v).label = none := by
  unfold solidC; split_ifs <;> exact ⟨rfl, rfl⟩

theorem dTerms_ub {V : Type*} [DecidableEq V] {p q : V} {cs : List (Comp V)}
    (h : ∀ c ∈ cs, c.label = none ∧ basB c = true) :
    ∀ d ∈ dTerms p q cs, ∀ c ∈ d, c.label = none ∧ basB c = true := by
  intro d hd c hc
  obtain ⟨j, hj, ps, hps, rfl⟩ := psteps_mem_dTerms.1 hd
  rcases List.mem_append.1 hc with h' | h'
  · exact h c (List.mem_of_mem_eraseIdx h')
  · rcases hk : cs[j] with ⟨κ, a, b, mi, l⟩
    rw [hk] at hps
    cases κ with
    | G ch => cases ch <;> simp [Comp.dPieces] at hps <;> subst hps <;> simp at h' <;>
        rcases h' with rfl | rfl <;> exact (basB_solidC _ _ _).symm
    | weight ch => cases ch <;> simp [Comp.dPieces] at hps <;> subst hps <;> simp at h' <;>
        rcases h' with rfl | rfl <;> exact (basB_solidC _ _ _).symm
    | light ch => cases ch <;> simp [Comp.dPieces] at hps <;> subst hps <;> simp at h' <;>
        rcases h' with rfl | rfl <;> exact (basB_solidC _ _ _).symm
    | _ => simp [Comp.dPieces] at hps

theorem ok_pLiftT {x : Atom k n} {g : Graph k n} {E : TExpansion k n}
    (hE : ∀ s ∈ E, ∀ c ∈ s.g.comps, c.label = none ∧ basB c = true) :
    ∀ t ∈ pLiftT x g E, OK t.g.comps := by
  intro t ht
  obtain ⟨s, hs, -, rfl⟩ := mem_pLiftT.1 ht
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    obtain ⟨hl, hb⟩ := hE s hs d hd
    unfold rl
    split_ifs with hr
    · exact Or.inr ⟨hr, by simpa [basB] using hb⟩
    · exact Or.inl hl
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    left
    simp [Comp.map, pEnv_unl g d hd]

theorem oWeightP2Pos_ub {x : Atom k n} {h : Graph k n} {E : TExpansion k n}
    (hh : ∀ c ∈ h.comps, c.label = none ∧ basB c = true) (hE : oWeightP2Pos x h = some E) :
    ∀ s ∈ E, ∀ c ∈ s.g.comps, c.label = none ∧ basB c = true := by
  intro s hs
  obtain ⟨i, hi, -, -, cs, co, rfl, hcs⟩ := mem_oWeightP2Pos hE hs
  have hl : ∀ L : List (Comp (Atom k n)), (∀ c ∈ L, c ∈ h.comps) →
      ∀ c ∈ liftCs 1 L, c.label = none ∧ basB c = true := by
    intro L hL c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    obtain ⟨h1, h2⟩ := hh c' (hL c' hc')
    exact ⟨by simp [Comp.map, h1], by rw [basB_map]; exact h2⟩
  have hm : ∀ (κ : Kind) (u v : Atom k (n + 1)), κ.isRandom = false ∨ κ = .light .plus ∨
      κ = .G .plus → (mkC κ u v).label = none ∧ basB (mkC κ u v) = true := by
    intro κ u v hκ
    rcases hκ with hκ | rfl | rfl
    · refine ⟨rfl, ?_⟩
      unfold basB; simp only [mkC, List.isEmpty_nil, Bool.true_and]
      cases κ <;> simp_all [Kind.isRandom]
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  simp only
  rcases hcs with rfl | rfl | ⟨j, hj, ps, hps, rfl⟩
  · intro c hc
    rcases List.mem_append.1 hc with h' | h'
    · exact hl _ (fun c hc => List.mem_of_mem_eraseIdx hc) c h'
    · simp at h'; rcases h' with rfl | rfl
      · exact hm _ _ _ (Or.inl rfl)
      · exact hm _ _ _ (Or.inr (Or.inl rfl))
  · intro c hc
    rcases List.mem_append.1 hc with h' | h'
    · exact hl _ (fun c hc => hc) c h'
    · simp at h'; rcases h' with rfl | rfl
      · exact hm _ _ _ (Or.inl rfl)
      · exact hm _ _ _ (Or.inr (Or.inl rfl))
  · intro c hc
    have hF := hl (h.comps.eraseIdx i) (fun c hc => List.mem_of_mem_eraseIdx hc)
    have hd : liftCs 1 ((h.comps.eraseIdx i).eraseIdx j) ++ ps ∈
        dTerms (newA 0) (liftA 1 x) (liftCs 1 (h.comps.eraseIdx i)) := by
      rw [psteps_mem_dTerms]
      refine ⟨j, by simpa [liftCs] using hj, ps, by simpa [liftCs] using hps, ?_⟩
      simp [liftCs, List.eraseIdx_map]
    rcases List.mem_append.1 hc with h' | h'
    · exact dTerms_ub hF _ hd c h'
    · simp at h'; rcases h' with rfl | rfl
      · exact hm _ _ _ (Or.inl rfl)
      · exact hm _ _ _ (Or.inr (Or.inr rfl))

/-- The value of `Õ^{(x),2}_weight` inside `P_x`. -/
theorem valueL {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hp : g.Plain) :
    TExpansion.ValueEq (oWeightP2T x g) g modelAdm := by
  unfold oWeightP2T
  rcases hE : oWeightP2Pos x g.pCore with _ | E
  · dsimp only
    rcases hE' : oWeightP2Pos x g.pCore.conj with _ | E'
    · dsimp only
      intro Ω ι _ _ PF D _ e
      funext ω
      simp [TExpansion.forget, Expansion.valR, Tracked.self]
    · dsimp only
      rw [pLiftT_conj]
      refine valueEq_conj ?_ (okP hlab hp) ?_
      · refine valueL_plain (lab_conj hlab) hp.conj ?_
        rw [pCore_conj]; exact hE'
      · refine ok_pLiftT (oWeightP2Pos_ub ?_ hE')
        intro c hc
        rw [← pCore_conj] at hc
        exact ⟨pCore_unl _ c hc, pCore_basB hp.conj c hc⟩
  · dsimp only
    exact valueL_plain hlab hp hE

end ValueL2

/-! ## Components at given positions -/

section PickErase

variable {α : Type*}

theorem zipIdx_nodup' (l : List α) : l.zipIdx.Nodup :=
  List.Nodup.of_map Prod.snd (zip_snd_nodup l)

theorem perm_pick_erase (is : List ℕ) (l : List α) :
    l.Perm (pickIdxs is l ++ eraseIdxs is l) := by
  unfold pickIdxs eraseIdxs
  rw [← List.map_append]
  conv_lhs => rw [← List.zipIdx_map_fst 0 l]
  exact ((List.filter_append_perm _ _).symm).map _

theorem zipIdx_filter_eq (l : List α) {i : ℕ} (hi : i < l.length) :
    (l.zipIdx.filter fun p => p.2 == i).Perm [(l[i], i)] := by
  rw [List.perm_ext_iff_of_nodup ((zipIdx_nodup' l).filter _) (List.nodup_singleton _)]
  rintro ⟨a, m⟩
  simp only [List.mem_filter, List.mem_zipIdx_iff_getElem?, beq_iff_eq, List.mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨h1, rfl⟩
    rw [List.getElem?_eq_getElem hi] at h1
    exact ⟨(Option.some.inj h1).symm, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨List.getElem?_eq_getElem hi, rfl⟩

theorem pick_cons_filter {is : List ℕ} {l : List α} {i : ℕ} (hi : i < l.length)
    (his : i ∈ is) : (pickIdxs is l).Perm (l[i] :: pickIdxs (is.filter (· != i)) l) := by
  unfold pickIdxs
  have h1 := (List.filter_append_perm (fun p : α × ℕ => p.2 == i)
    (l.zipIdx.filter fun p => is.contains p.2)).symm
  rw [List.filter_filter, List.filter_filter] at h1
  have e1 : (l.zipIdx.filter fun p => (p.2 == i) && is.contains p.2) =
      l.zipIdx.filter fun p => p.2 == i := by
    apply List.filter_congr
    intro p _
    by_cases h : p.2 = i
    · simp [h, his]
    · simp [h]
  have e2 : (l.zipIdx.filter fun p => !(p.2 == i) && is.contains p.2) =
      l.zipIdx.filter fun p => (is.filter (· != i)).contains p.2 := by
    apply List.filter_congr
    intro p _
    by_cases h : p.2 = i
    · simp [h]
    · simp [h, List.contains_iff_mem, List.mem_filter]
  rw [e1, e2] at h1
  have := (h1.trans ((zipIdx_filter_eq l hi).append_right _)).map Prod.fst
  simpa using this

theorem pickIdxs_single {l : List α} {i : ℕ} (hi : i < l.length) :
    (pickIdxs [i] l).Perm [l[i]] := by
  have := pick_cons_filter (is := [i]) hi (List.mem_singleton_self _)
  have e : pickIdxs ([i].filter (· != i)) l = [] := by
    simp [pickIdxs]
  rw [e] at this
  exact this

theorem pickIdxs_two {l : List α} {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (hij : i ≠ j) : (pickIdxs [i, j] l).Perm [l[i], l[j]] := by
  have h := pick_cons_filter (is := [i, j]) hi (by simp)
  have e : [i, j].filter (· != i) = [j] := by simp [Ne.symm hij]
  rw [e] at h
  exact h.trans (List.Perm.cons _ (pickIdxs_single hj))

end PickErase

/-! ## [II, (4.24)] inside `P_x`: terms moving edges at `x` to the new atom -/

section TermBase

variable {k n : ℕ}

/-- A solid edge with label `P_x` between `x` and `u`. -/
def EdgeAt (x u : Atom k n) (r : Comp (Atom k n)) : Prop :=
  r.kind.isSolid = true ∧ r.label = some (.P, x) ∧ ((r.x = x ∧ r.y = u) ∨ (r.x = u ∧ r.y = x))

/-- A component of kind `κ` with label `P` at the image of `x` between the new atom and `u`. -/
def NewEdge (x u : Atom k n) (κ : Kind) (a : Comp (Atom k (n + 1))) : Prop :=
  a.kind = κ ∧ a.minor = [] ∧ a.label = some (.P, liftA 1 x) ∧
    ((a.x = newA 0 ∧ a.y = liftA 1 u) ∨ (a.x = liftA 1 u ∧ a.y = newA 0))

theorem NewEdge.congr_kind {x u : Atom k n} {κ κ' : Kind} {a : Comp (Atom k (n + 1))}
    (h : NewEdge x u κ a) (e : κ = κ') : NewEdge x u κ' a := e ▸ h

theorem EdgeAt.facts {C : ℕ} {x u : Atom k n} {g : Graph k n} (hS : St C x g)
    {r : Comp (Atom k n)} (hr : r ∈ g.comps) (h : EdgeAt x u r) :
    u ≠ x ∧ ¬ g.SameBlock u x := by
  have hne := hS.nn.noLoop r hr h.1
  have hib := hS.nn.inBlk r hr h.1
  rcases h.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hne hib
  · exact ⟨Ne.symm hne, fun h' => hib (Graph.sameBlock_symm h')⟩
  · exact ⟨hne, hib⟩

theorem NewEdge.aok {x u : Atom k n} {g : Graph k n} {κ : Kind}
    {a : Comp (Atom k (n + 1))} (h : NewEdge x u κ a) (hκ : κ.isSolid = true) : AOK x g a := by
  obtain ⟨ch, hch⟩ := Kind.isSolid_iff.1 hκ
  exact aok_Gnew (h.1.trans hch) h.2.1 h.2.2.1 h.2.2.2

theorem NewEdge.touch {x u : Atom k n} {κ : Kind} {a : Comp (Atom k (n + 1))}
    (h : NewEdge x u κ a) : touchN a = true ∧ otherN a = liftA 1 u := by
  unfold touchN otherN
  rcases h.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · rw [h1, h2]
    simp [liftA_ne_newA]

theorem NewEdge.nx {x u : Atom k n} {κ : Kind} {a : Comp (Atom k (n + 1))}
    {g₁ : Graph k (n + 1)} (h : NewEdge x u κ a) (ha : a ∈ g₁.comps) (hκ : κ ≠ .xdot) :
    NX g₁ (newA 0) (liftA 1 u) :=
  NX.ends ha (by rw [h.1]; exact hκ) h.2.2.2

theorem NewEdge.bb {x u : Atom k n} {a : Comp (Atom k (n + 1))}
    {g₁ : Graph k (n + 1)} (h : NewEdge x u (.G .plus) a) (ha : a ∈ g₁.comps)
    (hu : u.isRight = true) : BB g₁ (newA 0) (liftA 1 u) := by
  refine BB.ends h.2.2.2 (BB_of_G ha h.1 ?_ ?_)
  · rcases h.2.2.2 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    · exact newA_isRight
    · rw [liftA_isRight]; exact hu
  · rcases h.2.2.2 with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2]
    · rw [liftA_isRight]; exact hu
    · exact newA_isRight

open Classical in
theorem NewEdge.wbp {x u : Atom k n} {g : Graph k n} {κ : Kind}
    {a : Comp (Atom k (n + 1))} {g₁ : Graph k (n + 1)} (h : NewEdge x u κ a)
    (hκ : κ.isSolid = true) (hu : ¬ g.SameBlock u x)
    (hblk : ∀ u v, g₁.SameBlock (liftA 1 u) (liftA 1 v) ↔ g.SameBlock u v)
    (hnew : ∀ b, g₁.SameBlock (newA 0) b ↔ b = newA 0) :
    wBP (fun v => g₁.SameBlock v (liftA 1 x)) a = 0 := by
  obtain ⟨ch, hch⟩ := Kind.isSolid_iff.1 hκ
  have hαx : ¬ g₁.SameBlock (newA 0) (liftA 1 x) := fun h' =>
    liftA_ne_newA 1 x 0 ((hnew _).1 h')
  rw [wBP_G (h.1.trans hch) (by rw [h.2.2.1]; rfl)]
  rcases h.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp [hαx, hblk, hu]

open Classical in
theorem EdgeAt.wbp {C : ℕ} {x u : Atom k n} {g : Graph k n} (hS : St C x g)
    {r : Comp (Atom k n)} (hr : r ∈ g.comps) (h : EdgeAt x u r) :
    wBP (fun v => g.SameBlock v x) r = 1 := by
  obtain ⟨-, hu⟩ := h.facts hS hr
  obtain ⟨ch, hch⟩ := Kind.isSolid_iff.1 h.1
  rw [wBP_G hch (by rw [h.2.1]; rfl)]
  rcases h.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
    simp [hu, Graph.sameBlock_refl]

/-- The main terms of [II, (4.24)] inside `P_x`: two edges at `x` moved to the new atom, with a
light weight at `x` or not. -/
theorem termBase2 {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {r₁ r₂ : Comp (Atom k n)} {rest : List (Comp (Atom k n))}
    (hR : g.comps.Perm ([r₁, r₂] ++ rest)) {u₁ u₂ : Atom k n}
    (h₁ : EdgeAt x u₁ r₁) (h₂ : EdgeAt x u₂ r₂)
    {a₁ a₂ : Comp (Atom k (n + 1))} (ha₁ : NewEdge x u₁ r₁.kind a₁)
    (ha₂ : NewEdge x u₂ r₂.kind a₂) {X : List (Comp (Atom k (n + 1)))}
    (hX : ∀ a ∈ X, ∃ ch, a = ⟨.light ch, liftA 1 x, liftA 1 x, [], some (.P, liftA 1 x)⟩)
    (hXl : X.length ≤ 1) {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++
      ([mkC (.waved .s) (liftA 1 x) (newA 0), a₁, a₂] ++ X)))
    (hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩) :
    PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
  have hN := hS.nn
  have hr₁ : r₁ ∈ g.comps := hR.symm.subset (by simp)
  have hr₂ : r₂ ∈ g.comps := hR.symm.subset (by simp)
  have hx₁ : (liftA 1 x).isRight = true := by rw [liftA_isRight]; exact hN.hx
  have hmem : ∀ a ∈ [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, a₂] ++ X, a ∈ g₁.comps :=
    fun a ha => hL.symm.subset (List.mem_append_right _ ha)
  have hsm := hmem (mkC (.waved .s) (liftA 1 x) (newA 0)) (by simp)
  have ha₁m := hmem a₁ (by simp)
  have ha₂m := hmem a₂ (by simp)
  have hs₁ : r₁.kind.isSolid = true := h₁.1
  have hs₂ : r₂.kind.isSolid = true := h₂.1
  obtain ⟨ch₁, hk₁⟩ := Kind.isSolid_iff.1 hs₁
  obtain ⟨ch₂, hk₂⟩ := Kind.isSolid_iff.1 hs₂
  have hXs : ∀ a ∈ X, a.kind.isSolid = false := by
    intro a ha; obtain ⟨ch, rfl⟩ := hX a ha; rfl
  have hNXs : NX g₁ (liftA 1 x) (newA 0) := NX.ends hsm (by simp [mkC]) (Or.inl ⟨rfl, rfl⟩)
  have hBs : BB g₁ (liftA 1 x) (newA 0) :=
    BB.ends (d := mkC (.waved .s) (liftA 1 x) (newA 0)) (Or.inl ⟨rfl, rfl⟩)
      (BB_of_mol hsm rfl hx₁ newA_isRight)
  have hcon1 : ∀ {r : Comp (Atom k n)} {u : Atom k n} {a : Comp (Atom k (n + 1))},
      EdgeAt x u r → NewEdge x u r.kind a → a ∈ g₁.comps →
      Relation.EqvGen (fun u v => ∃ d ∈ g₁.comps, d.kind ≠ .xdot ∧ d.x = u ∧ d.y = v)
        (liftA 1 r.x) (liftA 1 r.y) := by
    intro r u a hr ha ham
    have hp : NX g₁ (liftA 1 x) (liftA 1 u) :=
      hNXs.trans _ _ _ (ha.nx ham (Kind.ne_xdot_of_isRandom (Kind.isRandom_of_isSolid hr.1)))
    rcases hr.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hp
    · exact hp.symm
  have hblue1 : ∀ {r : Comp (Atom k n)} {u : Atom k n} {a : Comp (Atom k (n + 1))},
      EdgeAt x u r → NewEdge x u r.kind a → a ∈ g₁.comps → r.kind = .G .plus →
      ∀ i j, r.x = .inr i → r.y = .inr j →
        Relation.EqvGen (bconn g₁) (Fin.castAdd 1 i) (Fin.castAdd 1 j) := by
    intro r u a hr ha ham hk i j hi hj
    have hu : u.isRight = true := by
      rcases hr.2.2 with ⟨-, h2⟩ | ⟨h1, -⟩
      · rw [← h2, hj]; rfl
      · rw [← h1, hi]; rfl
    have hp : BB g₁ (liftA 1 x) (liftA 1 u) := hBs.trans ((hk ▸ ha).bb ham hu)
    have hp' : BB g₁ (liftA 1 r.x) (liftA 1 r.y) := by
      rcases hr.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      · exact hp
      · exact hp.symm
    obtain ⟨p, q, hp1, hq1, hpq⟩ := hp'
    rw [hi, liftA_inr] at hp1; rw [hj, liftA_inr] at hq1
    cases Sum.inr.inj hp1; cases Sum.inr.inj hq1
    exact hpq
  have hA : ∀ a ∈ [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, a₂] ++ X, AOK x g a := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact aok_sx
      · exact ha₁.aok hs₁
      · exact ha₂.aok hs₂
    · obtain ⟨ch, rfl⟩ := hX a ha
      exact aok_W (Or.inr rfl) rfl rfl rfl
  have hfN : (([mkC (.waved .s) (liftA 1 x) (newA 0), a₁, a₂] ++ X).filter fun a =>
      a.kind.isSolid && !touchN a) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · simp [mkC, Kind.isSolid]
      · simp [ha₁.touch.1]
      · simp [ha₂.touch.1]
    · simp [hXs a ha]
  have hfT : (([mkC (.waved .s) (liftA 1 x) (newA 0), a₁, a₂] ++ X).filter fun a =>
      a.kind.isSolid && touchN a) = [a₁, a₂] := by
    have hXf : X.filter (fun a => a.kind.isSolid && touchN a) = [] :=
      List.filter_eq_nil_iff.2 (fun a ha => by simp [hXs a ha])
    rw [List.filter_append, hXf, List.append_nil]
    simp [mkC, Kind.isSolid, ha₁.touch.1, ha₂.touch.1, ha₁.1, ha₂.1, hk₁, hk₂]
  have hordX : psteps_ordL X = X.length := by
    unfold psteps_ordL
    rw [show X.map (fun c => c.kind.ord) = X.map fun _ => (1 : ℤ) from
      List.map_congr_left fun a ha => by obtain ⟨ch, rfl⟩ := hX a ha; rfl]
    simp
  have hordR : psteps_ordL [r₁, r₂] = 2 := by
    simp [psteps_ordL, hk₁, hk₂, Kind.ord] <;> norm_num
  have hordA : psteps_ordL ([mkC (.waved .s) (liftA 1 x) (newA 0), a₁, a₂] ++ X) = 4 + X.length := by
    unfold psteps_ordL at hordX ⊢
    rw [List.map_append, List.sum_append, hordX]
    simp [mkC, Kind.ord, ha₁.1, ha₂.1, hk₁, hk₂] <;> ring
  refine termGen hS hR ?_ hL hA (by simp) ?_ ?_ hch ?_ (by rw [hfN]; simp) (by rw [hfT]; simp)
    ?_ ?_
  · intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact h₁.2.1
    · exact h₂.2.1
  · intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact hcon1 h₁ ha₁ ha₁m
    · exact hcon1 h₂ ha₂ ha₂m
  · intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact hblue1 h₁ ha₁ ha₁m
    · exact hblue1 h₂ ha₂ ha₂m
  · simp; omega
  · rw [hordR, hordA]; push_cast; linarith [(Nat.cast_nonneg X.length : (0 : ℤ) ≤ X.length)]
  · intro heq hlt
    rw [hordR, hordA] at heq
    have hX0 : X = [] := List.eq_nil_of_length_eq_zero (by push_cast at heq; omega)
    subst hX0
    obtain ⟨-, hu₁⟩ := h₁.facts hS hr₁
    obtain ⟨-, hu₂⟩ := h₂.facts hS hr₂
    refine ⟨?_, Or.inr (Or.inl ?_)⟩
    · simp only [List.append_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        wBP_none (a := mkC (.waved .s) (liftA 1 x) (newA 0)) rfl,
        ha₁.wbp hs₁ hu₁ hlt.blk hlt.blkNew, ha₂.wbp hs₂ hu₂ hlt.blk hlt.blkNew,
        h₁.wbp hS hr₁, h₂.wbp hS hr₂]
      norm_num
    · intro a ha has hat
      simp only [List.append_nil, List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · simp [mkC, Kind.isSolid] at has
      · rw [ha₁.touch.2, hlt.blk]; exact hu₁
      · rw [ha₂.touch.2, hlt.blk]; exact hu₂

/-- The term of [II, (4.24)] with one edge at `x` moved to the new atom and an edge between the new
atom and `x` added. -/
theorem termBase1 {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {r₁ : Comp (Atom k n)} {rest : List (Comp (Atom k n))}
    (hR : g.comps.Perm ([r₁] ++ rest)) {u₁ : Atom k n} (h₁ : EdgeAt x u₁ r₁)
    {a₁ b : Comp (Atom k (n + 1))} (ha₁ : NewEdge x u₁ r₁.kind a₁) {ch : Charge}
    (hb : NewEdge x x (.G ch) b) {g₁ : Graph k (n + 1)}
    (hL : g₁.comps.Perm (rest.map (Comp.map (liftA 1)) ++
      [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, b]))
    (hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩) :
    PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
  have hN := hS.nn
  have hx₁ : (liftA 1 x).isRight = true := by rw [liftA_isRight]; exact hN.hx
  have hmem : ∀ a ∈ [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, b], a ∈ g₁.comps :=
    fun a ha => hL.symm.subset (List.mem_append_right _ ha)
  have hsm := hmem (mkC (.waved .s) (liftA 1 x) (newA 0)) (by simp)
  have ha₁m := hmem a₁ (by simp)
  have hs₁ : r₁.kind.isSolid = true := h₁.1
  obtain ⟨ch₁, hk₁⟩ := Kind.isSolid_iff.1 hs₁
  have hNXs : NX g₁ (liftA 1 x) (newA 0) := NX.ends hsm (by simp [mkC]) (Or.inl ⟨rfl, rfl⟩)
  have hBs : BB g₁ (liftA 1 x) (newA 0) :=
    BB.ends (d := mkC (.waved .s) (liftA 1 x) (newA 0)) (Or.inl ⟨rfl, rfl⟩)
      (BB_of_mol hsm rfl hx₁ newA_isRight)
  have hA : ∀ a ∈ [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, b], AOK x g a := by
    intro a ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact aok_sx
    · exact ha₁.aok hs₁
    · exact hb.aok rfl
  refine termGen hS hR ?_ hL hA (by simp) ?_ ?_ hch (by simp) ?_ ?_ ?_ ?_
  · intro c hc
    rw [List.mem_singleton] at hc; subst hc; exact h₁.2.1
  · intro c hc
    rw [List.mem_singleton] at hc; subst hc
    have hp : NX g₁ (liftA 1 x) (liftA 1 u₁) :=
      hNXs.trans _ _ _ (ha₁.nx ha₁m (Kind.ne_xdot_of_isRandom (Kind.isRandom_of_isSolid hs₁)))
    rcases h₁.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact hp
    · exact hp.symm
  · intro c hc hk i j hi hj
    rw [List.mem_singleton] at hc; subst hc
    have hu : u₁.isRight = true := by
      rcases h₁.2.2 with ⟨-, h2⟩ | ⟨h1, -⟩
      · rw [← h2, hj]; rfl
      · rw [← h1, hi]; rfl
    have hp : BB g₁ (liftA 1 x) (liftA 1 u₁) := hBs.trans ((hk ▸ ha₁).bb ha₁m hu)
    have hp' : BB g₁ (liftA 1 c.x) (liftA 1 c.y) := by
      rcases h₁.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
      · exact hp
      · exact hp.symm
    obtain ⟨p, q, hp1, hq1, hpq⟩ := hp'
    rw [hi, liftA_inr] at hp1; rw [hj, liftA_inr] at hq1
    cases Sum.inr.inj hp1; cases Sum.inr.inj hq1
    exact hpq
  · rw [List.filter_eq_nil_iff.2]
    · simp
    intro a ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · simp [mkC, Kind.isSolid]
    · simp [ha₁.touch.1]
    · simp [hb.touch.1]
  · have : [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, b].filter (fun a =>
        a.kind.isSolid && touchN a) = [a₁, b] := by
      simp [mkC, Kind.isSolid, ha₁.touch.1, hb.touch.1, ha₁.1, hb.1, hk₁]
    rw [this]; simp
  · have : psteps_ordL [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, b] = 4 := by
      simp [psteps_ordL, mkC, Kind.ord, ha₁.1, hb.1, hk₁] <;> norm_num
    rw [this]; simp [psteps_ordL, hk₁, Kind.ord] <;> norm_num
  · intro heq
    have : psteps_ordL [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, b] = 4 := by
      simp [psteps_ordL, mkC, Kind.ord, ha₁.1, hb.1, hk₁] <;> norm_num
    rw [this] at heq
    simp [psteps_ordL, hk₁, Kind.ord] at heq <;> norm_num at heq

end TermBase

/-! ## [II, (4.24)] inside `P_x`: the shapes of the terms -/

section ShapeE

variable {k n : ℕ}

/-- A solid edge between `x` and `u`. -/
def EdgeH (x u : Atom k n) (r : Comp (Atom k n)) : Prop :=
  r.kind.isSolid = true ∧ ((r.x = x ∧ r.y = u) ∨ (r.x = u ∧ r.y = x))

/-- A component of kind `κ` between the new atom and `u`, without minor and label. -/
def NewH (u : Atom k n) (κ : Kind) (a : Comp (Atom k (n + 1))) : Prop :=
  a = mkC κ (newA 0) (liftA 1 u) ∨ a = mkC κ (liftA 1 u) (newA 0)

/-- The shapes of the terms of [II, (4.24)] at `x` applied to the components `H`, other than the
terms with the label `Q_x`: two edges at `x` moved to the new atom (with a light weight at `x` or
not); one edge moved and an edge between the new atom and `x` added; a light weight on the new
atom added; a derivative term. All with the waved edge between `x` and the new atom. -/
def ShapeE (x : Atom k n) (H : List (Comp (Atom k n)))
    (cs : List (Comp (Atom k (n + 1)))) : Prop :=
  (∃ (r₁ r₂ : Comp (Atom k n)) (B : List (Comp (Atom k n))) (u₁ u₂ : Atom k n)
      (a₁ a₂ : Comp (Atom k (n + 1))) (X : List (Comp (Atom k (n + 1)))),
      H.Perm ([r₁, r₂] ++ B) ∧ EdgeH x u₁ r₁ ∧ EdgeH x u₂ r₂ ∧ NewH u₁ r₁.kind a₁ ∧
      NewH u₂ r₂.kind a₂ ∧ (∀ a ∈ X, ∃ ch, a = mkC (.light ch) (liftA 1 x) (liftA 1 x)) ∧
      X.length ≤ 1 ∧
      cs = liftCs 1 B ++ ([mkC (.waved .s) (liftA 1 x) (newA 0), a₁, a₂] ++ X)) ∨
  (∃ (r₁ : Comp (Atom k n)) (B : List (Comp (Atom k n))) (u₁ : Atom k n)
      (a₁ b : Comp (Atom k (n + 1))) (ch : Charge),
      H.Perm ([r₁] ++ B) ∧ EdgeH x u₁ r₁ ∧ NewH u₁ r₁.kind a₁ ∧ NewH x (.G ch) b ∧
      (cs = liftCs 1 B ++ [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, b] ∨
        cs = liftCs 1 B ++ [mkC (.waved .s) (liftA 1 x) (newA 0), b, a₁])) ∨
  (∃ ch : Charge, cs = liftCs 1 H ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.light ch) (newA 0) (newA 0)]) ∨
  (∃ (r c : Comp (Atom k n)) (B : List (Comp (Atom k n))) (z : Atom k n) (p q : Atom k (n + 1))
      (ps : List (Comp (Atom k (n + 1)))) (e₀ : Comp (Atom k (n + 1))),
      H.Perm ([r, c] ++ B) ∧ EdgeH x z r ∧ c.kind.isRandom = true ∧
      (c.kind.isSolid = true → c.x ≠ x ∧ c.y ≠ x) ∧
      ((p = newA 0 ∧ q = liftA 1 x) ∨ (p = liftA 1 x ∧ q = newA 0)) ∧
      (c.map (liftA 1)).dPieces p q = some ps ∧ NewH z r.kind e₀ ∧
      cs = liftCs 1 B ++ (ps ++ [mkC (.waved .s) (liftA 1 x) (newA 0), e₀]))

theorem rl_mkC_random {V : Type*} (y : V) {κ : Kind} (h : κ.isRandom = true) (u v : V) :
    rl y (mkC κ u v) = ⟨κ, u, v, [], some (.P, y)⟩ := by
  simp [rl, mkC, h]

theorem rl_sx (x : Atom k n) :
    rl (liftA 1 x) (mkC (.waved .s) (liftA 1 x) (newA 0)) = mkC (.waved .s) (liftA 1 x) (newA 0) := by
  simp [rl, mkC, Kind.isRandom]

theorem NewH.newEdge {x u : Atom k n} {κ : Kind} {a : Comp (Atom k (n + 1))}
    (h : NewH u κ a) (hκ : κ.isRandom = true) : NewEdge x u κ (rl (liftA 1 x) a) := by
  rcases h with rfl | rfl <;> rw [rl_mkC_random _ hκ]
  · exact ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩

theorem EdgeH.edgeAt {x u : Atom k n} {r : Comp (Atom k n)} (h : EdgeH x u r) :
    EdgeAt x u (rl x r) := by
  have hr : r.kind.isRandom = true := Kind.isRandom_of_isSolid h.1
  refine ⟨by simp [rl, hr, h.1], by simp [rl, hr], ?_⟩
  simp only [rl, hr, ite_true]
  exact h.2

/-- The terms of the shapes `ShapeE`, read inside `P_x`, have the clauses `PStepsTermOK`. -/
theorem termShape {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    {cs : List (Comp (Atom k (n + 1)))} (hcs : ShapeE x g.pCore.comps cs) (co : Coeff)
    {g₁ : Graph k (n + 1)}
    (hg₁ : g₁ = ⟨cs.map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), co⟩)
    (hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨n + 1, g₁⟩) :
    PStepsTermOK (C + 5) x g ⟨n + 1, g₁, liftA 1⟩ := by
  subst hg₁
  have hN := hS.nn
  have hlab := hN.lab
  have hlr := hN.plain.labRand
  rcases hcs with ⟨r₁, r₂, B, u₁, u₂, a₁, a₂, X, hB, hr₁, hr₂, ha₁, ha₂, hX, hXl, rfl⟩ |
    ⟨r₁, B, u₁, a₁, b, ch, hB, hr₁, ha₁, hb, hcs⟩ | ⟨ch, rfl⟩ |
    ⟨r, c, B, z, p, q, ps, e₀, hB, hr, hc, hcx, hpq, hps, he, rfl⟩
  · obtain ⟨hR, hL⟩ := liftOut hlab hlr hB
      ([mkC (.waved .s) (liftA 1 x) (newA 0), a₁, a₂] ++ X)
    simp only [List.map_cons, List.map_nil] at hR
    rw [show ([mkC (.waved .s) (liftA 1 x) (newA 0), a₁, a₂] ++ X).map (rl (liftA 1 x)) =
      [mkC (.waved .s) (liftA 1 x) (newA 0), rl (liftA 1 x) a₁, rl (liftA 1 x) a₂] ++
        X.map (rl (liftA 1 x)) by simp [rl_sx]] at hL
    refine termBase2 hS hR hr₁.edgeAt hr₂.edgeAt
      ((ha₁.newEdge (Kind.isRandom_of_isSolid hr₁.1)).congr_kind ?_)
      ((ha₂.newEdge (Kind.isRandom_of_isSolid hr₂.1)).congr_kind ?_) (X := X.map (rl (liftA 1 x)))
      ?_ (by simpa using hXl) hL hch
    · simp [rl, Kind.isRandom_of_isSolid hr₁.1]
    · simp [rl, Kind.isRandom_of_isSolid hr₂.1]
    · intro a ha
      obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
      obtain ⟨ch, rfl⟩ := hX a' ha'
      exact ⟨ch, rl_mkC_random _ rfl _ _⟩
  · have hna : NewEdge x u₁ (rl x r₁).kind (rl (liftA 1 x) a₁) :=
      (ha₁.newEdge (x := x) (Kind.isRandom_of_isSolid hr₁.1)).congr_kind
        (show r₁.kind = (rl x r₁).kind by simp [rl, Kind.isRandom_of_isSolid hr₁.1])
    rcases hcs with rfl | rfl
    · obtain ⟨hR, hL⟩ := liftOut hlab hlr hB [mkC (.waved .s) (liftA 1 x) (newA 0), a₁, b]
      simp only [List.map_cons, List.map_nil] at hR
      rw [show ([mkC (.waved .s) (liftA 1 x) (newA 0), a₁, b] : List _).map (rl (liftA 1 x)) =
        [mkC (.waved .s) (liftA 1 x) (newA 0), rl (liftA 1 x) a₁, rl (liftA 1 x) b] by
          simp [rl_sx]] at hL
      exact termBase1 hS hR hr₁.edgeAt hna (hb.newEdge rfl) hL hch
    · obtain ⟨hR, hL⟩ := liftOut hlab hlr hB [mkC (.waved .s) (liftA 1 x) (newA 0), b, a₁]
      simp only [List.map_cons, List.map_nil] at hR
      rw [show ([mkC (.waved .s) (liftA 1 x) (newA 0), b, a₁] : List _).map (rl (liftA 1 x)) =
        [mkC (.waved .s) (liftA 1 x) (newA 0), rl (liftA 1 x) b, rl (liftA 1 x) a₁] by
          simp [rl_sx]] at hL
      exact termBase1 hS hR hr₁.edgeAt hna (hb.newEdge rfl)
        (hL.trans (List.Perm.append_left _ (List.Perm.cons _ (List.Perm.swap _ _ _)))) hch
  · have hB : g.pCore.comps.Perm ([] ++ g.pCore.comps) := by simp
    obtain ⟨hR, hL⟩ := liftOut hlab hlr hB
      [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light ch) (newA 0) (newA 0)]
    rw [show ([mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light ch) (newA 0) (newA 0)] :
        List _).map (rl (liftA 1 x)) = [mkC (.waved .s) (liftA 1 x) (newA 0),
          rl (liftA 1 x) (mkC (.light ch) (newA 0) (newA 0))] by simp [rl_sx]] at hL
    exact termLa hS hR (by simp) (Or.inl (by simp)) hL hch
  · obtain ⟨hR, hL⟩ := liftOut hlab hlr hB (ps ++ [mkC (.waved .s) (liftA 1 x) (newA 0), e₀])
    simp only [List.map_cons, List.map_nil] at hR
    obtain ⟨ch, hk⟩ := Kind.isSolid_iff.1 hr.1
    have hrr := hr.edgeAt
    have hrm : rl x r ∈ g.comps := hR.symm.subset (by simp)
    obtain ⟨-, hzx⟩ := hrr.facts hS hrm
    have hcr : (rl x c).label = some (.P, x) := by simp [rl, hc]
    refine termD hS hR hrr.2.1 hcr (Or.inr hzx) (ch := ch) (Or.inr ⟨by simp [rl, hk,
      Kind.isRandom], by simpa [rl, Kind.isRandom_of_isSolid hr.1] using hr.2⟩)
      (fun hs hx => absurd hx (by
        have := hcx (by simpa [rl, hc] using hs)
        simp only [rl, hc, ite_true]
        tauto)) hpq (by rw [dPieces_rl]; exact hps) (e₀ := e₀) ?_ ?_ hL hch
    · rcases he with rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · rcases he with rfl | rfl
      · simp [solidC, mkC, hk, Ne.symm (liftA_ne_newA 1 z 0)]
      · simp [solidC, mkC, hk, liftA_ne_newA 1 z 0]

end ShapeE

section ShapeConj

variable {k n : ℕ}

theorem Kind.conj_isSolid' (κ : Kind) : κ.conj.isSolid = κ.isSolid := by
  cases κ with
  | G ch => cases ch <;> rfl
  | weight ch => cases ch <;> rfl
  | light ch => cases ch <;> rfl
  | inv ch => cases ch <;> rfl
  | wD ch d => cases ch <;> rfl
  | waved w => cases w <;> rfl
  | _ => rfl

theorem EdgeH.conj {x u : Atom k n} {r : Comp (Atom k n)} (h : EdgeH x u r) :
    EdgeH x u (conjC r) :=
  ⟨by simp [conjC, Kind.conj_isSolid', h.1], h.2⟩

theorem NewH.conj {u : Atom k n} {κ : Kind} {a : Comp (Atom k (n + 1))}
    (h : NewH u κ a) : NewH u κ.conj (conjC a) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem ShapeE.conj {x : Atom k n} {H : List (Comp (Atom k n))}
    {cs : List (Comp (Atom k (n + 1)))} (h : ShapeE x H cs) :
    ShapeE x (H.map conjC) (cs.map conjC) := by
  rcases h with ⟨r₁, r₂, B, u₁, u₂, a₁, a₂, X, hB, hr₁, hr₂, ha₁, ha₂, hX, hXl, rfl⟩ |
    ⟨r₁, B, u₁, a₁, b, ch, hB, hr₁, ha₁, hb, hcs⟩ | ⟨ch, rfl⟩ |
    ⟨r, c, B, z, p, q, ps, e₀, hB, hr, hc, hcx, hpq, hps, he, rfl⟩
  · refine Or.inl ⟨conjC r₁, conjC r₂, B.map conjC, u₁, u₂, conjC a₁, conjC a₂, X.map conjC,
      by simpa using hB.map conjC, hr₁.conj, hr₂.conj, ha₁.conj, ha₂.conj, ?_, by simpa using hXl,
      ?_⟩
    · intro a ha
      obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
      obtain ⟨ch, rfl⟩ := hX a' ha'
      exact ⟨ch.flip, by cases ch <;> rfl⟩
    · simp [liftCs_conj, conjC_mkC, Kind.conj]
  · refine Or.inr (Or.inl ⟨conjC r₁, B.map conjC, u₁, conjC a₁, conjC b, ch.flip,
      by simpa using hB.map conjC, hr₁.conj, ha₁.conj, ?_, ?_⟩)
    · have := hb.conj
      cases ch <;> exact this
    · rcases hcs with rfl | rfl
      · left; simp [liftCs_conj, conjC_mkC, Kind.conj]
      · right; simp [liftCs_conj, conjC_mkC, Kind.conj]
  · refine Or.inr (Or.inr (Or.inl ⟨ch.flip, ?_⟩))
    simp only [List.map_append, liftCs_conj, List.map_cons, List.map_nil, conjC_mkC]
    cases ch <;> rfl
  · refine Or.inr (Or.inr (Or.inr ⟨conjC r, conjC c, B.map conjC, z, q, p, ps.map conjC,
      conjC e₀, by simpa using hB.map conjC, hr.conj, by simpa [conjC, Kind.conj_isRandom'] using hc,
      fun hs => hcx (by simpa [conjC, Kind.conj_isSolid'] using hs), ?_, ?_, he.conj, ?_⟩))
    · rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact Or.inl ⟨h2, h1⟩
    · rw [← dPieces_conj, conjC_map, conjC_conjC, hps]
      rfl
    · simp [liftCs_conj, conjC_mkC, Kind.conj]

end ShapeConj

/-! ## [II, (4.24)]: the terms have the shapes `ShapeE` -/

section ShapesOut

variable {k n : ℕ}

theorem edgeIdx_mem {x : Atom k n} {h : Graph k n} {ch : Charge} {out : Bool} {j : ℕ}
    (hj : j ∈ h.edgeIdx x ch out) :
    ∃ hjl : j < h.comps.length, ep x ch out (h.comps[j], j) = true := by
  rw [edgeIdx_eq] at hj
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
  obtain ⟨hpz, hpe⟩ := List.mem_filter.1 hp
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hpz)
  refine ⟨hlt, ?_⟩
  have : ((h.comps[p.2]'hlt), p.2) = p := Prod.ext hget rfl
  rw [this]; exact hpe

theorem ep_edgeH {x : Atom k n} {ch : Charge} {out : Bool} {p : Comp (Atom k n) × ℕ}
    (h : ep x ch out p = true) :
    p.1.kind = .G ch ∧ EdgeH x (if out then p.1.y else p.1.x) p.1 := by
  obtain ⟨hk, ho, hi⟩ := ep_spec x h
  refine ⟨hk, by rw [hk]; rfl, ?_⟩
  cases out
  · exact Or.inr ⟨rfl, (hi rfl).1⟩
  · exact Or.inl ⟨(ho rfl).1, rfl⟩

theorem labelQ_mem {V : Type*} (u : V) {L : List (Comp V)} {c : Comp V} (hc : c ∈ L)
    (hr : c.kind.isRandom = true) : ∃ c' ∈ labelQs u L, c'.label = some (.Q, u) :=
  ⟨Comp.labelQ u c, List.mem_map_of_mem hc, by simp [Comp.labelQ, hr]⟩

/-- Every term of `multiEOut` at `x` is a term with the label `Q_x` or of a shape `ShapeE`. -/
theorem shapesOut {x : Atom k n} {h : Graph k n}
    (hNL : ∀ c ∈ h.comps, c.kind.isSolid = true → c.x ≠ c.y)
    {E : TExpansion k n} (hE : multiEOut x h = some E) :
    ∀ s ∈ E, (∃ c ∈ s.g.comps, c.label = some (.Q, s.f x)) ∨
      ∃ cs co, s = PS_t1 cs co ∧ ShapeE x h.comps cs := by
  obtain ⟨i₁, is₂, e₁, hOP, hL, -, rfl⟩ := multiEOut_some x h hE
  have hi₁ : i₁ < h.comps.length := (List.getElem?_eq_some_iff.1 hL).1
  have he₁ : h.comps[i₁] = e₁ := (List.getElem?_eq_some_iff.1 hL).2
  have hep₁ : ep x .plus true (e₁, i₁) = true := e₁_ep hOP hL
  obtain ⟨hk₁, hE₁⟩ := ep_edgeH hep₁
  simp only [ite_true] at hE₁
  have hr₁ : e₁.kind.isRandom = true := by rw [hk₁]; rfl
  have he₁m : e₁ ∈ h.comps := List.mem_of_getElem? hL
  have hsx : PS_oSx x = mkC (.waved .s) (liftA 1 x) (newA 0) := rfl
  have hgy : PS_oGy e₁ = mkC e₁.kind (newA 0) (liftA 1 e₁.y) := by rw [hk₁]; rfl
  -- the main terms
  have gM : ∀ (j : ℕ) (ch : Charge) (out : Bool), j ∈ h.edgeIdx x ch out →
      (ch, out) ≠ (.plus, true) → ∀ X : List (Comp (Atom k (n + 1))),
        (∀ a ∈ X, ∃ ch, a = mkC (.light ch) (liftA 1 x) (liftA 1 x)) → X.length ≤ 1 →
      ShapeE x h.comps (liftCs 1 (eraseIdxs [i₁, j] h.comps) ++ [PS_oSx x, PS_oGy e₁,
        if out then mkC (.G ch) (newA 0) (liftA 1 (h.comps.getD j e₁).y)
        else mkC (.G ch) (liftA 1 (h.comps.getD j e₁).x) (newA 0)] ++ X) := by
    intro j ch out hj hne X hX hXl
    obtain ⟨hjl, hepj⟩ := edgeIdx_mem hj
    have hij : i₁ ≠ j := by
      rintro rfl
      rw [he₁] at hepj
      obtain ⟨h1, h2⟩ := ep_excl x hep₁ hepj
      exact hne (by rw [← h1, ← h2])
    have hgd : h.comps.getD j e₁ = h.comps[j] := by simp [hjl]
    obtain ⟨hkj, hEj⟩ := ep_edgeH hepj
    refine Or.inl ⟨e₁, h.comps[j], eraseIdxs [i₁, j] h.comps, e₁.y, _, PS_oGy e₁,
      if out then mkC (.G ch) (newA 0) (liftA 1 (h.comps.getD j e₁).y)
        else mkC (.G ch) (liftA 1 (h.comps.getD j e₁).x) (newA 0), X, ?_, hE₁,
      hEj, Or.inl hgy, ?_, hX, hXl, by simp [hsx]⟩
    · have := (perm_pick_erase [i₁, j] h.comps).trans
        ((pickIdxs_two hi₁ hjl hij).append_right _)
      rwa [he₁] at this
    · rw [hgd, hkj]
      cases out
      · exact Or.inr rfl
      · exact Or.inl rfl
  have gE : ∀ (b : Comp (Atom k (n + 1))) (ch : Charge), NewH x (.G ch) b →
      ShapeE x h.comps (liftCs 1 (h.comps.eraseIdx i₁) ++ [PS_oSx x, b, PS_oGy e₁]) := by
    intro b ch hb
    refine Or.inr (Or.inl ⟨e₁, h.comps.eraseIdx i₁, e₁.y, PS_oGy e₁, b, ch, ?_, hE₁, Or.inl hgy, hb,
      Or.inr rfl⟩)
    have := (List.getElem_cons_eraseIdx_perm hi₁).symm
    rwa [he₁] at this
  have gD : ∀ d ∈ PS_oDs x h i₁ e₁, ShapeE x h.comps d := by
    intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    obtain ⟨j, hj, ps, hps, rfl⟩ := psteps_mem_dTerms.1 hd'
    set fL := eraseIdxs (psteps_oXIdx x h) h.comps with hfL
    have hj' : j < fL.length := by simpa [liftCs] using hj
    have hc : (liftCs 1 fL)[j] = fL[j].map (liftA 1) := by simp [liftCs]
    rw [hc] at hps
    have hcr : fL[j].kind.isRandom = true := by
      have := dPieces_random hps; simpa [Comp.map] using this
    refine Or.inr (Or.inr (Or.inr ⟨e₁, fL[j], pickIdxs ((psteps_oXIdx x h).filter (· != i₁)) h.comps ++
      fL.eraseIdx j, e₁.y, newA 0, liftA 1 x, ps, PS_oGy e₁, ?_, hE₁, hcr, ?_,
      Or.inl ⟨rfl, rfl⟩, hps, Or.inl hgy, ?_⟩))
    · have h1 := perm_pick_erase (psteps_oXIdx x h) h.comps
      have hmem : i₁ ∈ psteps_oXIdx x h := by simp [psteps_oXIdx, hOP]
      have h2 := pick_cons_filter (l := h.comps) hi₁ hmem
      rw [he₁] at h2
      have h3 := List.getElem_cons_eraseIdx_perm hj'
      refine h1.trans ((h2.append h3.symm).trans ?_)
      simp only [List.cons_append, List.singleton_append]
      exact List.Perm.cons _ List.perm_middle
    · intro hs
      have hcm : fL[j] ∈ fL := List.getElem_mem hj'
      obtain ⟨p, hp, hpc⟩ := List.mem_map.1 hcm
      obtain ⟨hpz, hpn⟩ := List.mem_filter.1 hp
      rw [contains_oXIdx x h hpz] at hpn
      have hcX : cX x p = false := by simpa using hpn
      obtain ⟨ch, hk⟩ := Kind.isSolid_iff.1 hs
      have hne := hNL _ (fst_mem_of_zip hpz) (by rw [hpc]; exact hs)
      rw [hpc] at hne
      refine ⟨fun hx => ?_, fun hy => ?_⟩
      · have hy' : fL[j].y ≠ x := fun h' => hne (hx.trans h'.symm)
        have : ep x ch true p = true := by
          simp [ep, hpc, hk, hx, hy']
        rw [cX_of_ep x this] at hcX; cases hcX
      · have hx' : fL[j].x ≠ x := fun h' => hne (h'.trans hy.symm)
        have : ep x ch false p = true := by
          simp [ep, hpc, hk, hy, hx']
        rw [cX_of_ep x this] at hcX; cases hcX
    · simp only [PS_oDs, liftCs, List.map_append, List.eraseIdx_map, List.append_assoc, hsx]
  intro s hs
  unfold psteps_oOut at hs
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hs
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    exact labelQ_mem (liftA 1 x) (c := PS_oGy e₁) (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_singleton_self _))) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    split_ifs at hs
    · simp at hs
    · rw [List.mem_singleton] at hs; subst hs
      exact labelQ_mem (liftA 1 x) (c := PS_oGy e₁) (by simp [PS_oE2]) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    split_ifs at hs
    · simp at hs
    · rw [List.mem_singleton] at hs; subst hs
      exact labelQ_mem (liftA 1 x) (c := PS_oGy e₁) (by simp [PS_oE1]) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    rw [List.mem_singleton] at hs; subst hs
    exact labelQ_mem (liftA 1 x) (c := mkC (.light .plus) (newA 0) (newA 0)) (by simp [PS_oL3]) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hs
    exact labelQ_mem (liftA 1 x) (c := PS_oGy e₁) (by simp [PS_oBaseP]) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hs
    exact labelQ_mem (liftA 1 x) (c := PS_oGy e₁) (by simp [PS_oBaseM]) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    rw [List.mem_singleton] at hs; subst hs
    exact labelQ_mem _ he₁m hr₁
  rcases List.mem_append.1 hs with hs | hs
  swap
  · right
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hs
    exact ⟨d, _, rfl, gD d hd⟩
  rcases List.mem_append.1 hs with hs | hs
  swap
  · right
    split_ifs at hs
    · simp at hs
    · rw [List.mem_singleton] at hs; subst hs
      refine ⟨_, _, rfl, ?_⟩
      have := gE (mkC (.G .minus) (newA 0) (liftA 1 x)) .minus (Or.inl rfl)
      simpa [PS_oE2, PS_oSx] using this
  rcases List.mem_append.1 hs with hs | hs
  swap
  · right
    split_ifs at hs
    · simp at hs
    · rw [List.mem_singleton] at hs; subst hs
      refine ⟨_, _, rfl, ?_⟩
      have := gE (mkC (.G .plus) (liftA 1 x) (newA 0)) .plus (Or.inr rfl)
      simpa [PS_oE1, PS_oSx] using this
  rcases List.mem_append.1 hs with hs | hs
  swap
  · right
    rw [List.mem_singleton] at hs; subst hs
    exact ⟨_, _, rfl, Or.inr (Or.inr (Or.inl ⟨.plus, rfl⟩))⟩
  rcases List.mem_append.1 hs with hs | hs
  swap
  · right
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hs
    refine ⟨_, _, rfl, ?_⟩
    have := gM j .plus false hj (by simp)
      [mkC (.light .plus) (liftA 1 x) (liftA 1 x)] (fun a ha => ⟨.plus, by simpa using ha⟩)
      (by simp)
    simpa [PS_oBaseP] using this
  rcases List.mem_append.1 hs with hs | hs
  swap
  · right
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hs
    refine ⟨_, _, rfl, ?_⟩
    have := gM j .minus true hj (by simp)
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)] (fun a ha => ⟨.minus, by simpa using ha⟩)
      (by simp)
    simpa [PS_oBaseM] using this
  rcases List.mem_append.1 hs with hs | hs
  · right
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hs
    refine ⟨_, _, rfl, ?_⟩
    have := gM j .minus true hj (by simp) [] (by simp) (by simp)
    simpa [PS_oBaseM] using this
  · right
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hs
    refine ⟨_, _, rfl, ?_⟩
    have := gM j .plus false hj (by simp) [] (by simp) (by simp)
    simpa [PS_oBaseP] using this

end ShapesOut

section ShapesIn

variable {k n : ℕ}

/-- Every term of `multiEIn` at `x`, when no solid edge leaves `x`, is a term with the label `Q_x`
or of a shape `ShapeE`. -/
theorem shapesIn {x : Atom k n} {h : Graph k n}
    (hNL : ∀ c ∈ h.comps, c.kind.isSolid = true → c.x ≠ c.y)
    (hout : ∀ ch, h.edgeIdx x ch true = [])
    {E : TExpansion k n} (hE : multiEIn x h = some E) :
    ∀ s ∈ E, (∃ c ∈ s.g.comps, c.label = some (.Q, s.f x)) ∨
      ∃ cs co, s = PS_t1 cs co ∧ ShapeE x h.comps cs := by
  obtain ⟨i₁, is₂, e₁, hIP, hL, -, rfl⟩ := multiEIn_some x h hE
  have hi₁ : i₁ < h.comps.length := (List.getElem?_eq_some_iff.1 hL).1
  have he₁ : h.comps[i₁] = e₁ := (List.getElem?_eq_some_iff.1 hL).2
  have hep₁ : ep x .plus false (e₁, i₁) = true := in_e₁_ep hIP hL
  obtain ⟨hk₁, hE₁⟩ := ep_edgeH hep₁
  simp only [Bool.false_eq_true, ite_false] at hE₁
  have hr₁ : e₁.kind.isRandom = true := by rw [hk₁]; rfl
  have he₁m : e₁ ∈ h.comps := List.mem_of_getElem? hL
  have hsx : PS_oSx x = mkC (.waved .s) (liftA 1 x) (newA 0) := rfl
  have hgw : PS_iGw e₁ = mkC e₁.kind (liftA 1 e₁.x) (newA 0) := by rw [hk₁]; rfl
  have gM : ∀ (j : ℕ) (ch : Charge), j ∈ h.edgeIdx x ch false → ch ≠ .plus →
      ∀ X : List (Comp (Atom k (n + 1))),
        (∀ a ∈ X, ∃ ch, a = mkC (.light ch) (liftA 1 x) (liftA 1 x)) → X.length ≤ 1 →
      ShapeE x h.comps (liftCs 1 (eraseIdxs [i₁, j] h.comps) ++ [PS_oSx x, PS_iGw e₁,
        mkC (.G ch) (liftA 1 (h.comps.getD j e₁).x) (newA 0)] ++ X) := by
    intro j ch hj hne X hX hXl
    obtain ⟨hjl, hepj⟩ := edgeIdx_mem hj
    have hij : i₁ ≠ j := by
      rintro rfl
      rw [he₁] at hepj
      obtain ⟨h1, -⟩ := ep_excl x hep₁ hepj
      exact hne h1.symm
    have hgd : h.comps.getD j e₁ = h.comps[j] := by simp [hjl]
    obtain ⟨hkj, hEj⟩ := ep_edgeH hepj
    refine Or.inl ⟨e₁, h.comps[j], eraseIdxs [i₁, j] h.comps, e₁.x, _, PS_iGw e₁,
      mkC (.G ch) (liftA 1 (h.comps.getD j e₁).x) (newA 0), X, ?_, hE₁,
      hEj, Or.inr hgw, ?_, hX, hXl, by simp [hsx]⟩
    · have := (perm_pick_erase [i₁, j] h.comps).trans
        ((pickIdxs_two hi₁ hjl hij).append_right _)
      rwa [he₁] at this
    · rw [hgd, hkj]
      exact Or.inr rfl
  have gD : ∀ d ∈ PS_iDs x h i₁ e₁, ShapeE x h.comps d := by
    intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    obtain ⟨j, hj, ps, hps, rfl⟩ := psteps_mem_dTerms.1 hd'
    set fL := eraseIdxs (psteps_iXIdx x h) h.comps with hfL
    have hj' : j < fL.length := by simpa [liftCs] using hj
    have hc : (liftCs 1 fL)[j] = fL[j].map (liftA 1) := by simp [liftCs]
    rw [hc] at hps
    have hcr : fL[j].kind.isRandom = true := by
      have := dPieces_random hps; simpa [Comp.map] using this
    refine Or.inr (Or.inr (Or.inr ⟨e₁, fL[j], pickIdxs ((psteps_iXIdx x h).filter (· != i₁)) h.comps ++
      fL.eraseIdx j, e₁.x, liftA 1 x, newA 0, ps, PS_iGw e₁, ?_, hE₁, hcr, ?_,
      Or.inr ⟨rfl, rfl⟩, hps, Or.inr hgw, ?_⟩))
    · have h1 := perm_pick_erase (psteps_iXIdx x h) h.comps
      have hmem : i₁ ∈ psteps_iXIdx x h := by simp [psteps_iXIdx, hIP]
      have h2 := pick_cons_filter (l := h.comps) hi₁ hmem
      rw [he₁] at h2
      have h3 := List.getElem_cons_eraseIdx_perm hj'
      refine h1.trans ((h2.append h3.symm).trans ?_)
      simp only [List.cons_append, List.singleton_append]
      exact List.Perm.cons _ List.perm_middle
    · intro hs
      have hcm : fL[j] ∈ fL := List.getElem_mem hj'
      obtain ⟨p, hp, hpc⟩ := List.mem_map.1 hcm
      obtain ⟨hpz, hpn⟩ := List.mem_filter.1 hp
      rw [contains_iXIdx x h hpz] at hpn
      have hcI : cI x p = false := by simpa using hpn
      obtain ⟨ch, hk⟩ := Kind.isSolid_iff.1 hs
      have hne := hNL _ (fst_mem_of_zip hpz) (by rw [hpc]; exact hs)
      rw [hpc] at hne
      refine ⟨fun hx => ?_, fun hy => ?_⟩
      · have hy' : fL[j].y ≠ x := fun h' => hne (hx.trans h'.symm)
        have : ep x ch true p = true := by
          simp [ep, hpc, hk, hx, hy']
        have hmem' : p.2 ∈ h.edgeIdx x ch true := by
          rw [edgeIdx_eq]; exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hpz, this⟩, rfl⟩
        rw [hout ch] at hmem'; simp at hmem'
      · have hx' : fL[j].x ≠ x := fun h' => hne (h'.trans hy.symm)
        have : ep x ch false p = true := by
          simp [ep, hpc, hk, hy, hx']
        have : cI x p = true := by
          cases ch <;> simp [cI, this]
        rw [this] at hcI; cases hcI
    · simp only [PS_iDs, liftCs, List.map_append, List.eraseIdx_map, List.append_assoc, hsx]
  intro s hs
  unfold psteps_iOut at hs
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hs
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    exact labelQ_mem (liftA 1 x) (c := PS_iGw e₁) (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_singleton_self _))) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    split_ifs at hs
    · simp at hs
    · rw [List.mem_singleton] at hs; subst hs
      exact labelQ_mem (liftA 1 x) (c := PS_iGw e₁) (by simp [PS_iE1]) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    rw [List.mem_singleton] at hs; subst hs
    exact labelQ_mem (liftA 1 x) (c := mkC (.light .plus) (newA 0) (newA 0)) (by simp [PS_oL3]) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hs
    exact labelQ_mem (liftA 1 x) (c := PS_iGw e₁) (by simp [PS_iBaseM]) rfl
  rcases List.mem_append.1 hs with hs | hs
  swap
  · left
    rw [List.mem_singleton] at hs; subst hs
    exact labelQ_mem _ he₁m hr₁
  rcases List.mem_append.1 hs with hs | hs
  swap
  · right
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hs
    exact ⟨d, _, rfl, gD d hd⟩
  rcases List.mem_append.1 hs with hs | hs
  swap
  · right
    split_ifs at hs
    · simp at hs
    · rw [List.mem_singleton] at hs; subst hs
      refine ⟨_, _, rfl, Or.inr (Or.inl ⟨e₁, h.comps.eraseIdx i₁, e₁.x, PS_iGw e₁,
        mkC (.G .plus) (newA 0) (liftA 1 x), .plus, ?_, hE₁, Or.inr hgw, Or.inl rfl,
        Or.inl rfl⟩)⟩
      have := (List.getElem_cons_eraseIdx_perm hi₁).symm
      rwa [he₁] at this
  rcases List.mem_append.1 hs with hs | hs
  swap
  · right
    rw [List.mem_singleton] at hs; subst hs
    exact ⟨_, _, rfl, Or.inr (Or.inr (Or.inl ⟨.plus, rfl⟩))⟩
  rcases List.mem_append.1 hs with hs | hs
  · right
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hs
    refine ⟨_, _, rfl, ?_⟩
    have := gM j .minus hj (by simp) [] (by simp) (by simp)
    simpa [PS_iBaseM] using this
  · right
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hs
    refine ⟨_, _, rfl, ?_⟩
    have := gM j .minus hj (by simp)
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)] (fun a ha => ⟨.minus, by simpa using ha⟩)
      (by simp)
    simpa [PS_iBaseM] using this

end ShapesIn

/-! ## [II, (4.24)] inside `P_x`: the clauses on the terms -/

section TermsE

variable {k n : ℕ}

theorem Kind.conj_eq_G (κ : Kind) (ch : Charge) : κ.conj = .G ch ↔ κ = .G ch.flip := by
  cases κ with
  | G c => cases c <;> cases ch <;> simp [Kind.conj, Charge.flip]
  | weight c => cases c <;> simp [Kind.conj]
  | light c => cases c <;> simp [Kind.conj]
  | inv c => cases c <;> simp [Kind.conj]
  | wD c d => cases c <;> simp [Kind.conj]
  | waved w => cases w <;> simp [Kind.conj]
  | _ => simp [Kind.conj]

theorem psteps_edgeIdx_conj (g : Graph k n) (x : Atom k n) (ch : Charge) (out : Bool) :
    g.conj.edgeIdx x ch out = g.edgeIdx x ch.flip out := by
  unfold Graph.edgeIdx
  rw [Graph.conj_comps', List.zipIdx_map, List.filter_map, List.map_map]
  have : (Prod.snd ∘ Prod.map conjC id : Comp (Atom k n) × ℕ → ℕ) = Prod.snd := rfl
  rw [this]
  congr 1
  apply List.filter_congr
  intro p _
  simp only [Function.comp_apply, Prod.map_fst, conjC]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Kind.conj_eq_G]

theorem noLoop_core {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g) :
    ∀ c ∈ g.pCore.comps, c.kind.isSolid = true → c.x ≠ c.y := by
  intro c hc hs
  obtain ⟨d, hd, -, rfl⟩ := pCore_mem hc
  exact hS.nn.noLoop d hd hs

/-- Every term of `Ô^{(x)}_multi-e` on `𝒢` is a term with the label `Q_x` or of a shape
`ShapeE`. -/
theorem shapes_multiEHat {x : Atom k n} {h : Graph k n}
    (hNL : ∀ c ∈ h.comps, c.kind.isSolid = true → c.x ≠ c.y)
    {E : TExpansion k n} (hE : multiEHat x h = some E) :
    ∀ s ∈ E, (∃ c ∈ s.g.comps, c.label = some (.Q, s.f x)) ∨
      ∃ cs co, s = PS_t1 cs co ∧ ShapeE x h.comps cs := by
  have hNL' : ∀ c ∈ h.conj.comps, c.kind.isSolid = true → c.x ≠ c.y := by
    intro c hc hs
    rw [Graph.conj_comps'] at hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    exact hNL d hd (by simpa [conjC, Kind.conj_isSolid'] using hs)
  have hconj : ∀ E' : TExpansion k n, (∀ s ∈ E', (∃ c ∈ s.g.comps, c.label = some (.Q, s.f x)) ∨
      ∃ cs co, s = PS_t1 cs co ∧ ShapeE x h.conj.comps cs) →
      ∀ s ∈ E'.conj, (∃ c ∈ s.g.comps, c.label = some (.Q, s.f x)) ∨
        ∃ cs co, s = PS_t1 cs co ∧ ShapeE x h.comps cs := by
    intro E' hE' s hs
    obtain ⟨s', hs', rfl⟩ := mem_TExpansion_conj.1 hs
    rcases hE' s' hs' with ⟨c, hc, hl⟩ | ⟨cs, co, rfl, hsh⟩
    · left
      exact ⟨conjC c, by rw [Graph.conj_comps']; exact List.mem_map_of_mem hc, hl⟩
    · right
      refine ⟨cs.map conjC, Coeff.conj co, rfl, ?_⟩
      have := hsh.conj
      rwa [Graph.conj_comps', map_conjC_conjC] at this
  unfold multiEHat at hE
  split_ifs at hE with h1 h2 h3 h4
  · exact shapesOut hNL hE
  · obtain ⟨E', hE', rfl⟩ := Option.map_eq_some_iff.1 hE
    exact hconj E' (shapesOut hNL' hE')
  · refine shapesIn hNL (fun ch => ?_) hE
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, not_not] at h1 h2
    cases ch
    · exact h1
    · exact h2
  · obtain ⟨E', hE', rfl⟩ := Option.map_eq_some_iff.1 hE
    refine hconj E' (shapesIn hNL' (fun ch => ?_) hE')
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, not_not] at h1 h2
    rw [psteps_edgeIdx_conj]
    cases ch
    · exact h2
    · exact h1

/-- The terms of [II, (4.24)] inside `P_x` have the clauses `PStepsTermOK`. -/
theorem termsE {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g)
    (hP : g.IsPFormAt x) {E : TExpansion k n} (hE : multiEHat x g.pCore = some E) :
    ∀ t ∈ pLiftT x g E, PStepsTermOK (C + 5) x g t := by
  intro t ht
  have hch : Relation.ReflTransGen QElemStep ⟨n, g⟩ ⟨t.nOut, t.g⟩ :=
    .single (QElemStep.pMultiE x g E t hP hS.nn.plain hE ht)
  obtain ⟨s, hs, hq, rfl⟩ := mem_pLiftT.1 ht
  rcases shapes_multiEHat (noLoop_core hS) hE s hs with ⟨c, hc, hl⟩ | ⟨cs, co, rfl, hsh⟩
  · exfalso
    have := List.any_eq_false.1 hq c hc
    simp [hl] at this
  · exact termShape hS hsh co rfl hch

end TermsE

/-! ## The value of [II, (4.24)] inside `P_x`: the families of terms -/

section PBlocks

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ}

/-- `P_x` of a factor times a light weight at `x`, split as the weight minus `m`. -/
theorem P_light_split (ω : Ω) (X : ι) {R : Ω → ℂ} (hR : A.Test R) (ch : Charge) :
    PF.P X (fun ω' => R ω' * ch.apply (A.G ω' X X - msc A.z)) ω =
      PF.P X (fun ω' => R ω' * ch.apply (A.G ω' X X)) ω - ch.apply (msc A.z) * PF.P X R ω := by
  have hG : A.Test fun ω' => R ω' * ch.apply (A.G ω' X X) := by
    cases ch
    · exact test_mul' A hR (test_G A _ _)
    · exact test_mul' A hR (test_star' A (test_G A _ _))
  rw [P_congr' (f := fun ω' => R ω' * ch.apply (A.G ω' X X - msc A.z))
    (g := fun ω' => R ω' * ch.apply (A.G ω' X X) - ch.apply (msc A.z) * R ω')
    (fun ω' => by cases ch <;> simp [Charge.apply] <;> ring),
    P_sub' A (good_of_test A hG) (good_of_test A (test_mul' A (test_const' A _) hR)),
    P_cmul' A _ (good_of_test A hR)]

theorem core_plainB {g : Graph k n} (hp : g.Plain) :
    ∀ c ∈ g.pCore.comps, c.isPlainB = true := by
  intro c hc
  obtain ⟨d, hd, -, rfl⟩ := pCore_mem hc
  obtain ⟨h1, h2, h3, -⟩ := hp d hd
  unfold Comp.isPlainB
  simp only [h1, List.isEmpty_nil, Option.isNone_none, Bool.true_and]

variable (x : Atom k n) (g : Graph k n) (i₁ : ℕ) (e₁ : Comp (Atom k n)) (e : Fin k → ι) (ω : Ω)

theorem PBM (hp : g.Plain) (j : ℕ) (s : Fin n → ι) :
    T1 PF D e ω ⟨(PS_oBaseM x g.pCore i₁ e₁ j).map (rl (liftA 1 x)) ++
        g.pEnv.map (Comp.map (liftA 1)), cm * cmb * g.pCore.coeff⟩ s +
      T1 PF D e ω ⟨(PS_oBaseM x g.pCore i₁ e₁ j ++ [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]).map
        (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), cm * g.pCore.coeff⟩ s =
    pv (D ω) (Sum.elim e s) g.pEnv * ∑ α, msc A.z * g.pCore.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s)
        (eraseIdxs [i₁, j] g.pCore.comps) * (A.G ω' α (Sum.elim e s e₁.y) *
          star (A.G ω' α (Sum.elim e s (g.pCore.comps.getD j e₁).y))) *
        star (A.G ω' (Sum.elim e s x) (Sum.elim e s x))) ω := by
  have hpl := core_plainB hp
  have hU : Unl g.pCore.comps := plain_Unl hpl
  have hUM : Unl (PS_oBaseM x g.pCore i₁ e₁ j) := by
    unfold PS_oBaseM PS_oSx PS_oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_eraseIdxs hc),
      by simp [Unl, mkC]⟩
  have hUM' : Unl (PS_oBaseM x g.pCore i₁ e₁ j ++ [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) :=
    Unl_append.2 ⟨hUM, by simp [Unl, mkC]⟩
  rw [T1_plift A x g _ _ hUM, T1_plift A x g _ _ hUM', ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  have hRt : A.Test fun ω' => rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
      (A.G ω' α (Sum.elim e s e₁.y) *
        star (A.G ω' α (Sum.elim e s (g.pCore.comps.getD j e₁).y))) :=
    test_mul' A (rv_test A _ _ fun c hc => (basB_of_plain (hpl c (mem_eraseIdxs hc))).1)
      (test_mul' A (test_G A _ _) (test_star' A (test_G A _ _)))
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (PS_oBaseM x g.pCore i₁ e₁ j) =
      rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.G ω' α (Sum.elim e s e₁.y) *
          star (A.G ω' α (Sum.elim e s (g.pCore.comps.getD j e₁).y))) := by
    intro ω'
    simp only [PS_oBaseM, PS_oSx, PS_oGy, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hrv' : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (PS_oBaseM x g.pCore i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) =
      (rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.G ω' α (Sum.elim e s e₁.y) *
          star (A.G ω' α (Sum.elim e s (g.pCore.comps.getD j e₁).y)))) *
        Charge.minus.apply (A.G ω' (Sum.elim e s x) (Sum.elim e s x) - msc A.z) := by
    intro ω'
    rw [rv_append, hrv]
    simp [Kind.isRandom, val_light A]
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (PS_oBaseM x g.pCore i₁ e₁ j) =
      dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [PS_oBaseM, PS_oSx, PS_oGy, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  have hdv' : dv (D ω) (Sum.elim e (Fin.append s ![α])) (PS_oBaseM x g.pCore i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) =
      dv (D ω) (Sum.elim e (Fin.append s ![α])) (PS_oBaseM x g.pCore i₁ e₁ j) := by
    simp [Kind.isRandom]
  rw [hdv', hdv, P_congr' hrv, P_congr' hrv', P_light_split A ω _ hRt .minus]
  simp only [ceval_mul, ceval_cm, ceval_cmb, Charge.apply]
  ring

theorem PBP (hp : g.Plain) (j : ℕ) (s : Fin n → ι) :
    T1 PF D e ω ⟨(PS_oBaseP x g.pCore i₁ e₁ j).map (rl (liftA 1 x)) ++
        g.pEnv.map (Comp.map (liftA 1)), cm * cm * g.pCore.coeff⟩ s +
      T1 PF D e ω ⟨(PS_oBaseP x g.pCore i₁ e₁ j ++ [mkC (.light .plus) (liftA 1 x) (liftA 1 x)]).map
        (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), cm * g.pCore.coeff⟩ s =
    pv (D ω) (Sum.elim e s) g.pEnv * ∑ α, msc A.z * g.pCore.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s)
        (eraseIdxs [i₁, j] g.pCore.comps) * (A.G ω' α (Sum.elim e s e₁.y) *
          A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α) *
        A.G ω' (Sum.elim e s x) (Sum.elim e s x)) ω := by
  have hpl := core_plainB hp
  have hU : Unl g.pCore.comps := plain_Unl hpl
  have hUM : Unl (PS_oBaseP x g.pCore i₁ e₁ j) := by
    unfold PS_oBaseP PS_oSx PS_oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_eraseIdxs hc),
      by simp [Unl, mkC]⟩
  have hUM' : Unl (PS_oBaseP x g.pCore i₁ e₁ j ++ [mkC (.light .plus) (liftA 1 x) (liftA 1 x)]) :=
    Unl_append.2 ⟨hUM, by simp [Unl, mkC]⟩
  rw [T1_plift A x g _ _ hUM, T1_plift A x g _ _ hUM', ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  have hRt : A.Test fun ω' => rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
      (A.G ω' α (Sum.elim e s e₁.y) * A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α) :=
    test_mul' A (rv_test A _ _ fun c hc => (basB_of_plain (hpl c (mem_eraseIdxs hc))).1)
      (test_mul' A (test_G A _ _) (test_G A _ _))
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (PS_oBaseP x g.pCore i₁ e₁ j) =
      rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.G ω' α (Sum.elim e s e₁.y) * A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α) := by
    intro ω'
    simp only [PS_oBaseP, PS_oSx, PS_oGy, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hrv' : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (PS_oBaseP x g.pCore i₁ e₁ j ++
      [mkC (.light .plus) (liftA 1 x) (liftA 1 x)]) =
      (rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.G ω' α (Sum.elim e s e₁.y) * A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α)) *
        Charge.plus.apply (A.G ω' (Sum.elim e s x) (Sum.elim e s x) - msc A.z) := by
    intro ω'
    rw [rv_append, hrv]
    simp [Kind.isRandom, val_light A]
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (PS_oBaseP x g.pCore i₁ e₁ j) =
      dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [PS_oBaseP, PS_oSx, PS_oGy, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  have hdv' : dv (D ω) (Sum.elim e (Fin.append s ![α])) (PS_oBaseP x g.pCore i₁ e₁ j ++
      [mkC (.light .plus) (liftA 1 x) (liftA 1 x)]) =
      dv (D ω) (Sum.elim e (Fin.append s ![α])) (PS_oBaseP x g.pCore i₁ e₁ j) := by
    simp [Kind.isRandom]
  rw [hdv', hdv, P_congr' hrv, P_congr' hrv', P_light_split A ω _ hRt .plus]
  simp only [ceval_mul, ceval_cm, Charge.apply]
  ring

end PBlocks

section PBlocks2

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ}
  (x : Atom k n) (g : Graph k n) (i₁ : ℕ) (e₁ : Comp (Atom k n)) (e : Fin k → ι) (ω : Ω)

theorem PBL (hp : g.Plain) (s : Fin n → ι) :
    T1 PF D e ω ⟨(PS_oL3 x g.pCore).map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)),
      cm * g.pCore.coeff⟩ s =
    pv (D ω) (Sum.elim e s) g.pEnv * ∑ α, msc A.z * g.pCore.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) g.pCore.comps * (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) g.pCore.comps *
        (A.G ω' α α - msc A.z)) ω := by
  have hU : Unl g.pCore.comps := plain_Unl (core_plainB hp)
  have hU3 : Unl (PS_oL3 x g.pCore) := by
    unfold PS_oL3 PS_oSx
    exact Unl_append.2 ⟨Unl_liftCs 1 hU, by simp [Unl, mkC]⟩
  rw [T1_plift A x g _ _ hU3]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (PS_oL3 x g.pCore) =
      rv (D ω') (Sum.elim e s) g.pCore.comps * (A.G ω' α α - msc A.z) := by
    intro ω'
    simp only [PS_oL3, PS_oSx, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_light A,
      elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (PS_oL3 x g.pCore) =
      dv (D ω) (Sum.elim e s) g.pCore.comps * (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [PS_oL3, PS_oSx, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  rw [P_congr' hrv, hdv, ceval_mul, ceval_cm]

theorem PBE1 (hp : g.Plain) (b : Prop) [Decidable b] (a : ℕ) (hb : b → a = 0)
    (s : Fin n → ι) :
    (if b then 0 else T1 PF D e ω ⟨(PS_oE1 x g.pCore i₁ e₁).map (rl (liftA 1 x)) ++
      g.pEnv.map (Comp.map (liftA 1)), (a : Coeff) * cm * g.pCore.coeff⟩ s) =
    pv (D ω) (Sum.elim e s) g.pEnv * ∑ α, (a : ℂ) * msc A.z * g.pCore.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) * (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) *
        (A.G ω' (Sum.elim e s x) α * A.G ω' α (Sum.elim e s e₁.y))) ω := by
  by_cases hb' : b
  · simp [hb', hb hb']
  rw [if_neg hb']
  have hU : Unl g.pCore.comps := plain_Unl (core_plainB hp)
  have hU3 : Unl (PS_oE1 x g.pCore i₁ e₁) := by
    unfold PS_oE1 PS_oSx PS_oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => List.mem_of_mem_eraseIdx hc),
      by simp [Unl, mkC]⟩
  rw [T1_plift A x g _ _ hU3]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (PS_oE1 x g.pCore i₁ e₁) =
      rv (D ω') (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) *
        (A.G ω' (Sum.elim e s x) α * A.G ω' α (Sum.elim e s e₁.y)) := by
    intro ω'
    simp only [PS_oE1, PS_oSx, PS_oGy, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (PS_oE1 x g.pCore i₁ e₁) =
      dv (D ω) (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) * (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [PS_oE1, PS_oSx, PS_oGy, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  rw [P_congr' hrv, hdv, ceval_mul, ceval_mul, ceval_cm, ceval_nat]

theorem PBE2 (hp : g.Plain) (b : Prop) [Decidable b] (a : ℕ) (hb : b → a = 0)
    (s : Fin n → ι) :
    (if b then 0 else T1 PF D e ω ⟨(PS_oE2 x g.pCore i₁ e₁).map (rl (liftA 1 x)) ++
      g.pEnv.map (Comp.map (liftA 1)), (a : Coeff) * cm * g.pCore.coeff⟩ s) =
    pv (D ω) (Sum.elim e s) g.pEnv * ∑ α, (a : ℂ) * msc A.z * g.pCore.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) * (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) *
        (star (A.G ω' α (Sum.elim e s x)) * A.G ω' α (Sum.elim e s e₁.y))) ω := by
  by_cases hb' : b
  · simp [hb', hb hb']
  rw [if_neg hb']
  have hU : Unl g.pCore.comps := plain_Unl (core_plainB hp)
  have hU3 : Unl (PS_oE2 x g.pCore i₁ e₁) := by
    unfold PS_oE2 PS_oSx PS_oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => List.mem_of_mem_eraseIdx hc),
      by simp [Unl, mkC]⟩
  rw [T1_plift A x g _ _ hU3]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (PS_oE2 x g.pCore i₁ e₁) =
      rv (D ω') (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) *
        (star (A.G ω' α (Sum.elim e s x)) * A.G ω' α (Sum.elim e s e₁.y)) := by
    intro ω'
    simp only [PS_oE2, PS_oSx, PS_oGy, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (PS_oE2 x g.pCore i₁ e₁) =
      dv (D ω) (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) * (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [PS_oE2, PS_oSx, PS_oGy, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  rw [P_congr' hrv, hdv, ceval_mul, ceval_mul, ceval_cm, ceval_nat]

theorem PBD (L : List (List (Comp (Atom k (n + 1))))) (hL : ∀ d ∈ L, Unl d)
    (s : Fin n → ι) :
    (L.map fun d => T1 PF D e ω ⟨d.map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)),
      cm * g.pCore.coeff⟩ s).sum =
    pv (D ω) (Sum.elim e s) g.pEnv * (L.map fun d => ∑ α, msc A.z * g.pCore.coeff.eval (msc A.z) *
      dv (D ω) (Sum.elim e (Fin.append s ![α])) d *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e (Fin.append s ![α])) d) ω).sum := by
  rw [← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun d hd => ?_)
  rw [T1_plift A x g _ _ (hL d hd), ceval_mul, ceval_cm]

end PBlocks2

/-! ## The value of [II, (4.24)] inside `P_x`, case (i) -/

section ValueEOut

variable {k n : ℕ}

theorem pLiftT_ite (x : Atom k n) (g : Graph k n) (b : Prop) [Decidable b]
    (E : TExpansion k n) : pLiftT x g (if b then [] else E) = if b then [] else pLiftT x g E := by
  split_ifs <;> rfl

theorem pLiftT_map_Q (x : Atom k n) (g : Graph k n) {β : Type*} (l : List β)
    (G : β → List (Comp (Atom k (n + 1)))) (d : β → Coeff)
    (hG : ∀ j ∈ l, ∃ c ∈ G j, c.kind.isRandom = true) :
    pLiftT x g (l.map fun j => PS_t1 (labelQs (liftA 1 x) (G j)) (d j)) = [] := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.map_cons]
    have hq : ((PS_t1 (labelQs (liftA 1 x) (G j)) (d j)).g.comps.any fun c =>
        decide (c.label = some (.Q, (PS_t1 (labelQs (liftA 1 x) (G j)) (d j)).f x))) = true := by
      obtain ⟨c, hc, hr⟩ := hG j (List.mem_cons_self ..)
      simp only [PS_t1, List.any_eq_true, decide_eq_true_eq]
      exact ⟨Comp.labelQ (liftA 1 x) c, List.mem_map_of_mem hc, by simp [Comp.labelQ, hr]⟩
    have ih' := ih fun j' hj' => hG j' (List.mem_cons_of_mem _ hj')
    unfold pLiftT at ih' ⊢
    rw [List.filterMap_cons, if_pos hq, ih']

theorem pLiftT_t0Q (x : Atom k n) (g : Graph k n) (cs : List (Comp (Atom k n)))
    (co : Coeff) (h : ∃ c ∈ cs, c.kind.isRandom = true) :
    pLiftT x g [⟨n, ⟨labelQs x cs, co⟩, id⟩] = [] := by
  have hq : ((⟨n, ⟨labelQs x cs, co⟩, id⟩ : Tracked k n).g.comps.any fun c =>
      decide (c.label = some (.Q, (⟨n, ⟨labelQs x cs, co⟩, id⟩ : Tracked k n).f x))) = true := by
    obtain ⟨c, hc, hr⟩ := h
    simp only [List.any_eq_true, decide_eq_true_eq]
    exact ⟨Comp.labelQ x c, List.mem_map_of_mem hc, by simp [Comp.labelQ, hr]⟩
  unfold pLiftT
  rw [List.filterMap_cons, if_pos hq]
  rfl

theorem pLiftT_single_Q (x : Atom k n) (g : Graph k n) (cs : List (Comp (Atom k (n + 1))))
    (d : Coeff) (h : ∃ c ∈ cs, c.kind.isRandom = true) :
    pLiftT x g [PS_t1 (labelQs (liftA 1 x) cs) d] = [] :=
  pLiftT_map_Q x g [()] (fun _ => cs) (fun _ => d) (fun _ _ => h)

theorem pLiftT_single_t1 (x : Atom k n) (g : Graph k n) (cs : List (Comp (Atom k (n + 1))))
    (d : Coeff) (hcs : Unl cs) :
    pLiftT x g [PS_t1 cs d] = [PS_t1 (cs.map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1))) d] := by
  rw [pLiftT_cons_t1 x g _ _ hcs, pLiftT_nil]

/-- The value of the multi-edge expansion [II, (4.24)] (case (i)) inside `P_x`. -/
theorem valueEOut_plain {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hp : g.Plain)
    {E : TExpansion k n} (hE : multiEOut x g.pCore = some E) :
    TExpansion.ValueEq (pLiftT x g E) g modelAdm := by
  intro Ω ι _ _ PF D hA e
  obtain ⟨A⟩ := hA
  funext ω
  obtain ⟨i₁, is₂, e₁, hOP, hL, hX, hEq⟩ := multiEOut_some x g.pCore hE
  rw [hEq]
  clear hE hEq
  have hpl := core_plainB hp
  have hU : Unl g.pCore.comps := plain_Unl hpl
  have he₁m : e₁ ∈ g.pCore.comps := List.mem_of_getElem? hL
  have hr₁ : e₁.kind.isRandom = true := by rw [(ep_spec x (e₁_ep hOP hL)).1]; rfl
  have hUM : ∀ j, Unl (PS_oBaseM x g.pCore i₁ e₁ j) := fun j => by
    unfold PS_oBaseM PS_oSx PS_oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_eraseIdxs hc),
      by simp [Unl, mkC]⟩
  have hUP : ∀ j, Unl (PS_oBaseP x g.pCore i₁ e₁ j) := fun j => by
    unfold PS_oBaseP PS_oSx PS_oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_eraseIdxs hc),
      by simp [Unl, mkC]⟩
  have hU3 : Unl (PS_oL3 x g.pCore) := by
    unfold PS_oL3 PS_oSx
    exact Unl_append.2 ⟨Unl_liftCs 1 hU, by simp [Unl, mkC]⟩
  have hUE1 : Unl (PS_oE1 x g.pCore i₁ e₁) := by
    unfold PS_oE1 PS_oSx PS_oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => List.mem_of_mem_eraseIdx hc),
      by simp [Unl, mkC]⟩
  have hUE2 : Unl (PS_oE2 x g.pCore i₁ e₁) := by
    unfold PS_oE2 PS_oSx PS_oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => List.mem_of_mem_eraseIdx hc),
      by simp [Unl, mkC]⟩
  have hFb : ∀ c ∈ eraseIdxs (psteps_oXIdx x g.pCore) g.pCore.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  have hUD : ∀ d ∈ PS_oDs x g.pCore i₁ e₁, Unl d := by
    intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    refine Unl_append.2 ⟨Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_pickIdxs hc),
      dTerms_unl (fun c hc => (plain_bas_lift hFb 1 c hc).2) d' hd'⟩, by simp [Unl, PS_oSx, PS_oGy, mkC]⟩
  have hgy : ∃ c ∈ [PS_oSx x, PS_oGy e₁], c.kind.isRandom = true := ⟨PS_oGy e₁, by simp, rfl⟩
  -- the terms with a label `Q_x` are dropped
  change S PF D e ω (pLiftT x g (psteps_oOut x g.pCore i₁ is₂ e₁)) = g.valR PF D e ω
  unfold psteps_oOut
  simp only [pLiftT_append, pLiftT_ite]
  rw [pLiftT_t0Q x g _ _ ⟨e₁, he₁m, hr₁⟩,
    pLiftT_map_Q x g _ (fun d => d) _ (fun d hd => by
      obtain ⟨d', -, rfl⟩ := List.mem_map.1 hd
      exact ⟨PS_oGy e₁, by simp, rfl⟩),
    pLiftT_map_Q x g _ (fun j => PS_oBaseM x g.pCore i₁ e₁ j ++
      [mkC (.weight .minus) (liftA 1 x) (liftA 1 x)]) _ (fun j _ => ⟨PS_oGy e₁, by simp [PS_oBaseM], rfl⟩),
    pLiftT_map_Q x g _ (fun j => PS_oBaseP x g.pCore i₁ e₁ j ++
      [mkC (.weight .plus) (liftA 1 x) (liftA 1 x)]) _ (fun j _ => ⟨PS_oGy e₁, by simp [PS_oBaseP], rfl⟩),
    pLiftT_single_Q x g _ _ ⟨mkC (.light .plus) (newA 0) (newA 0), by simp [PS_oL3], rfl⟩,
    pLiftT_single_Q x g _ _ ⟨PS_oGy e₁, by simp [PS_oE1], rfl⟩,
    pLiftT_single_Q x g _ _ ⟨PS_oGy e₁, by simp [PS_oE2], rfl⟩,
    pLiftT_single_t1 x g _ _ hU3, pLiftT_single_t1 x g _ _ hUE1, pLiftT_single_t1 x g _ _ hUE2,
    pLiftT_map_t1 x g _ (fun j => PS_oBaseM x g.pCore i₁ e₁ j) _ (fun j _ => hUM j),
    pLiftT_map_t1 x g _ (fun j => PS_oBaseP x g.pCore i₁ e₁ j) _ (fun j _ => hUP j),
    pLiftT_map_t1 x g _ (fun j => PS_oBaseM x g.pCore i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) _
      (fun j _ => Unl_append.2 ⟨hUM j, by simp [Unl, mkC]⟩),
    pLiftT_map_t1 x g _ (fun j => PS_oBaseP x g.pCore i₁ e₁ j ++
      [mkC (.light .plus) (liftA 1 x) (liftA 1 x)]) _
      (fun j _ => Unl_append.2 ⟨hUP j, by simp [Unl, mkC]⟩),
    pLiftT_map_t1 x g _ (fun d => d) _ hUD]
  simp only [ite_self, List.append_nil, S_append, S_map_t1, S_t1, S_ite, ite_sum]
  rw [valR_T0, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hdj : ∀ (ch : Charge) (out : Bool), ∀ j ∈ g.pCore.edgeIdx x ch out,
      dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) =
        dv (D ω) (Sum.elim e s) g.pCore.comps := by
    intro ch out j hj
    rw [edgeIdx_eq] at hj
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hj
    exact out_D3 _ hOP hL (D ω) (List.mem_filter.1 hq).1 (cX_of_ep x (List.mem_filter.1 hq).2)
  have hdE := out_D1 (Sum.elim e s) hOP hL (D ω)
  have hdD : ∀ d ∈ PS_oDs x g.pCore i₁ e₁, ∀ α, dv (D ω) (Sum.elim e (Fin.append s ![α])) d =
      dv (D ω) (Sum.elim e s) g.pCore.comps * (A.S (Sum.elim e s x) α : ℂ) := by
    intro d hd α
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have h2 := ((dTerms_spec A (Sum.elim e (Fin.append s ![α])) (newA 0) (liftA 1 x) _
      (plain_bas_lift hFb 1)).1 d' hd').2 (D ω)
    rw [dv_liftCs, elim_append_comp_liftA, out_D4] at h2
    simp only [dv_append, dv_liftCs, elim_append_comp_liftA, out_D5, h2, PS_oSx, PS_oGy, dv_cons,
      dv_nil, mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  have hM : ((g.pCore.edgeIdx x .minus true).map fun j => T1 PF D e ω
      ⟨(PS_oBaseM x g.pCore i₁ e₁ j).map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)),
        cm * cmb * g.pCore.coeff⟩ s).sum +
      ((g.pCore.edgeIdx x .minus true).map fun j => T1 PF D e ω
      ⟨(PS_oBaseM x g.pCore i₁ e₁ j ++ [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]).map
        (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), cm * g.pCore.coeff⟩ s).sum =
      pv (D ω) (Sum.elim e s) g.pEnv * ((g.pCore.edgeIdx x .minus true).map fun j => ∑ α,
        msc A.z * g.pCore.coeff.eval (msc A.z) *
        (dv (D ω) (Sum.elim e s) g.pCore.comps * (A.S (Sum.elim e s x) α : ℂ)) *
        PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s)
          (eraseIdxs [i₁, j] g.pCore.comps) * (A.G ω' α (Sum.elim e s e₁.y) *
            star (A.G ω' α (Sum.elim e s (g.pCore.comps.getD j e₁).y))) *
          star (A.G ω' (Sum.elim e s x) (Sum.elim e s x))) ω).sum := by
    rw [← List.sum_map_add, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    rw [PBM A x g i₁ e₁ e ω hp j s, hdj .minus true j hj]
  have hP : ((g.pCore.edgeIdx x .plus false).map fun j => T1 PF D e ω
      ⟨(PS_oBaseP x g.pCore i₁ e₁ j).map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)),
        cm * cm * g.pCore.coeff⟩ s).sum +
      ((g.pCore.edgeIdx x .plus false).map fun j => T1 PF D e ω
      ⟨(PS_oBaseP x g.pCore i₁ e₁ j ++ [mkC (.light .plus) (liftA 1 x) (liftA 1 x)]).map
        (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), cm * g.pCore.coeff⟩ s).sum =
      pv (D ω) (Sum.elim e s) g.pEnv * ((g.pCore.edgeIdx x .plus false).map fun j => ∑ α,
        msc A.z * g.pCore.coeff.eval (msc A.z) *
        (dv (D ω) (Sum.elim e s) g.pCore.comps * (A.S (Sum.elim e s x) α : ℂ)) *
        PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s)
          (eraseIdxs [i₁, j] g.pCore.comps) * (A.G ω' α (Sum.elim e s e₁.y) *
            A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α) *
          A.G ω' (Sum.elim e s x) (Sum.elim e s x)) ω).sum := by
    rw [← List.sum_map_add, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    rw [PBP A x g i₁ e₁ e ω hp j s, hdj .plus false j hj]
  have hL3 := PBL A x g e ω hp s
  have hE1 := PBE1 A x g i₁ e₁ e ω hp (is₂.isEmpty = true) is₂.length
    (fun h => by simpa using h) s
  have hE2 := PBE2 A x g i₁ e₁ e ω hp ((g.pCore.edgeIdx x .minus false).length = 0)
    (g.pCore.edgeIdx x .minus false).length id s
  rw [hdE] at hE1 hE2
  have hD := (PBD A x g e ω _ hUD s).trans (congrArg _ (congrArg List.sum (List.map_congr_left
    fun d hd => Finset.sum_congr rfl fun α _ => by rw [hdD d hd α])))
  have hT0 : T0 PF D e ω g s = g.pCore.coeff.eval (msc A.z) * dv (D ω) (Sum.elim e s) g.pCore.comps *
      pv (D ω) (Sum.elim e s) g.pEnv *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) g.pCore.comps) ω := by
    rw [T0, termR_pform A hlab hp.labRand, m_eq A]
    rfl
  have hcore := out_core A hpl hOP hL hX (Sum.elim e s) (fun α => Sum.elim e (Fin.append s ![α]))
    (fun α => elim_append_comp_liftA e s ![α]) (fun α => by simp) ω
  rw [Q_apply'] at hcore
  linear_combination hM + hP + hL3 + hE1 + hE2 + hD - hT0 -
    pv (D ω) (Sum.elim e s) g.pEnv * hcore

end ValueEOut

section PBlocksIn

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ}
  (x : Atom k n) (g : Graph k n) (i₁ : ℕ) (e₁ : Comp (Atom k n)) (e : Fin k → ι) (ω : Ω)

theorem PBMi (hp : g.Plain) (j : ℕ) (s : Fin n → ι) :
    T1 PF D e ω ⟨(PS_iBaseM x g.pCore i₁ e₁ j).map (rl (liftA 1 x)) ++
        g.pEnv.map (Comp.map (liftA 1)), cm * cmb * g.pCore.coeff⟩ s +
      T1 PF D e ω ⟨(PS_iBaseM x g.pCore i₁ e₁ j ++ [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]).map
        (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), cm * g.pCore.coeff⟩ s =
    pv (D ω) (Sum.elim e s) g.pEnv * ∑ α, msc A.z * g.pCore.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s)
        (eraseIdxs [i₁, j] g.pCore.comps) * (A.G ω' (Sum.elim e s e₁.x) α *
          star (A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α)) *
        star (A.G ω' (Sum.elim e s x) (Sum.elim e s x))) ω := by
  have hpl := core_plainB hp
  have hU : Unl g.pCore.comps := plain_Unl hpl
  have hUM : Unl (PS_iBaseM x g.pCore i₁ e₁ j) := by
    unfold PS_iBaseM PS_oSx PS_iGw
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_eraseIdxs hc),
      by simp [Unl, mkC]⟩
  have hUM' : Unl (PS_iBaseM x g.pCore i₁ e₁ j ++ [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) :=
    Unl_append.2 ⟨hUM, by simp [Unl, mkC]⟩
  rw [T1_plift A x g _ _ hUM, T1_plift A x g _ _ hUM', ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  have hRt : A.Test fun ω' => rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
      (A.G ω' (Sum.elim e s e₁.x) α *
        star (A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α)) :=
    test_mul' A (rv_test A _ _ fun c hc => (basB_of_plain (hpl c (mem_eraseIdxs hc))).1)
      (test_mul' A (test_G A _ _) (test_star' A (test_G A _ _)))
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (PS_iBaseM x g.pCore i₁ e₁ j) =
      rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.G ω' (Sum.elim e s e₁.x) α *
          star (A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α)) := by
    intro ω'
    simp only [PS_iBaseM, PS_oSx, PS_iGw, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hrv' : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (PS_iBaseM x g.pCore i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) =
      (rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.G ω' (Sum.elim e s e₁.x) α *
          star (A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α))) *
        Charge.minus.apply (A.G ω' (Sum.elim e s x) (Sum.elim e s x) - msc A.z) := by
    intro ω'
    rw [rv_append, hrv]
    simp [Kind.isRandom, val_light A]
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (PS_iBaseM x g.pCore i₁ e₁ j) =
      dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) *
        (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [PS_iBaseM, PS_oSx, PS_iGw, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  have hdv' : dv (D ω) (Sum.elim e (Fin.append s ![α])) (PS_iBaseM x g.pCore i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) =
      dv (D ω) (Sum.elim e (Fin.append s ![α])) (PS_iBaseM x g.pCore i₁ e₁ j) := by
    simp [Kind.isRandom]
  rw [hdv', hdv, P_congr' hrv, P_congr' hrv', P_light_split A ω _ hRt .minus]
  simp only [ceval_mul, ceval_cm, ceval_cmb, Charge.apply]
  ring

theorem PBE1i (hp : g.Plain) (b : Prop) [Decidable b] (a : ℕ) (hb : b → a = 0)
    (s : Fin n → ι) :
    (if b then 0 else T1 PF D e ω ⟨(PS_iE1 x g.pCore i₁ e₁).map (rl (liftA 1 x)) ++
      g.pEnv.map (Comp.map (liftA 1)), (a : Coeff) * cm * g.pCore.coeff⟩ s) =
    pv (D ω) (Sum.elim e s) g.pEnv * ∑ α, (a : ℂ) * msc A.z * g.pCore.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) * (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) *
        (A.G ω' (Sum.elim e s e₁.x) α * A.G ω' α (Sum.elim e s x))) ω := by
  by_cases hb' : b
  · simp [hb', hb hb']
  rw [if_neg hb']
  have hU : Unl g.pCore.comps := plain_Unl (core_plainB hp)
  have hU3 : Unl (PS_iE1 x g.pCore i₁ e₁) := by
    unfold PS_iE1 PS_oSx PS_iGw
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => List.mem_of_mem_eraseIdx hc),
      by simp [Unl, mkC]⟩
  rw [T1_plift A x g _ _ hU3]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (PS_iE1 x g.pCore i₁ e₁) =
      rv (D ω') (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) *
        (A.G ω' (Sum.elim e s e₁.x) α * A.G ω' α (Sum.elim e s x)) := by
    intro ω'
    simp only [PS_iE1, PS_oSx, PS_iGw, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (PS_iE1 x g.pCore i₁ e₁) =
      dv (D ω) (Sum.elim e s) (g.pCore.comps.eraseIdx i₁) * (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [PS_iE1, PS_oSx, PS_iGw, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  rw [P_congr' hrv, hdv, ceval_mul, ceval_mul, ceval_cm, ceval_nat]

end PBlocksIn

section ValueEIn

variable {k n : ℕ}

/-- The value of the multi-edge expansion [II, (4.24)] (case (iii)) inside `P_x`. -/
theorem valueEIn_plain {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hp : g.Plain)
    {E : TExpansion k n} (hE : multiEIn x g.pCore = some E) :
    TExpansion.ValueEq (pLiftT x g E) g modelAdm := by
  intro Ω ι _ _ PF D hA e
  obtain ⟨A⟩ := hA
  funext ω
  obtain ⟨i₁, is₂, e₁, hIP, hL, hX, hEq⟩ := multiEIn_some x g.pCore hE
  rw [hEq]
  clear hE hEq
  have hpl := core_plainB hp
  have hU : Unl g.pCore.comps := plain_Unl hpl
  have he₁m : e₁ ∈ g.pCore.comps := List.mem_of_getElem? hL
  have hr₁ : e₁.kind.isRandom = true := by rw [(ep_spec x (in_e₁_ep hIP hL)).1]; rfl
  have hUM : ∀ j, Unl (PS_iBaseM x g.pCore i₁ e₁ j) := fun j => by
    unfold PS_iBaseM PS_oSx PS_iGw
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_eraseIdxs hc),
      by simp [Unl, mkC]⟩
  have hU3 : Unl (PS_oL3 x g.pCore) := by
    unfold PS_oL3 PS_oSx
    exact Unl_append.2 ⟨Unl_liftCs 1 hU, by simp [Unl, mkC]⟩
  have hUE1 : Unl (PS_iE1 x g.pCore i₁ e₁) := by
    unfold PS_iE1 PS_oSx PS_iGw
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => List.mem_of_mem_eraseIdx hc),
      by simp [Unl, mkC]⟩
  have hFb : ∀ c ∈ eraseIdxs (psteps_iXIdx x g.pCore) g.pCore.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  have hUD : ∀ d ∈ PS_iDs x g.pCore i₁ e₁, Unl d := by
    intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    refine Unl_append.2 ⟨Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_pickIdxs hc),
      dTerms_unl (fun c hc => (plain_bas_lift hFb 1 c hc).2) d' hd'⟩, by simp [Unl, PS_oSx, PS_iGw, mkC]⟩
  change S PF D e ω (pLiftT x g (psteps_iOut x g.pCore i₁ is₂ e₁)) = g.valR PF D e ω
  unfold psteps_iOut
  simp only [pLiftT_append, pLiftT_ite]
  rw [pLiftT_t0Q x g _ _ ⟨e₁, he₁m, hr₁⟩,
    pLiftT_map_Q x g _ (fun d => d) _ (fun d hd => by
      obtain ⟨d', -, rfl⟩ := List.mem_map.1 hd
      exact ⟨PS_iGw e₁, by simp, rfl⟩),
    pLiftT_map_Q x g _ (fun j => PS_iBaseM x g.pCore i₁ e₁ j ++
      [mkC (.weight .minus) (liftA 1 x) (liftA 1 x)]) _ (fun j _ => ⟨PS_iGw e₁, by simp [PS_iBaseM], rfl⟩),
    pLiftT_single_Q x g _ _ ⟨mkC (.light .plus) (newA 0) (newA 0), by simp [PS_oL3], rfl⟩,
    pLiftT_single_Q x g _ _ ⟨PS_iGw e₁, by simp [PS_iE1], rfl⟩,
    pLiftT_single_t1 x g _ _ hU3, pLiftT_single_t1 x g _ _ hUE1,
    pLiftT_map_t1 x g _ (fun j => PS_iBaseM x g.pCore i₁ e₁ j) _ (fun j _ => hUM j),
    pLiftT_map_t1 x g _ (fun j => PS_iBaseM x g.pCore i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) _
      (fun j _ => Unl_append.2 ⟨hUM j, by simp [Unl, mkC]⟩),
    pLiftT_map_t1 x g _ (fun d => d) _ hUD]
  simp only [ite_self, List.append_nil, S_append, S_map_t1, S_t1, S_ite, ite_sum]
  rw [valR_T0, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hdj : ∀ j ∈ g.pCore.edgeIdx x .minus false,
      dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] g.pCore.comps) =
        dv (D ω) (Sum.elim e s) g.pCore.comps := by
    intro j hj
    rw [edgeIdx_eq] at hj
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hj
    exact in_D3 _ hIP hL (D ω) (List.mem_filter.1 hq).1
      (by simp [cI, (List.mem_filter.1 hq).2])
  have hdE := in_D1 (Sum.elim e s) hIP hL (D ω)
  have hdD : ∀ d ∈ PS_iDs x g.pCore i₁ e₁, ∀ α, dv (D ω) (Sum.elim e (Fin.append s ![α])) d =
      dv (D ω) (Sum.elim e s) g.pCore.comps * (A.S (Sum.elim e s x) α : ℂ) := by
    intro d hd α
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have h2 := ((dTerms_spec A (Sum.elim e (Fin.append s ![α])) (liftA 1 x) (newA 0) _
      (plain_bas_lift hFb 1)).1 d' hd').2 (D ω)
    rw [dv_liftCs, elim_append_comp_liftA, in_D4] at h2
    simp only [dv_append, dv_liftCs, elim_append_comp_liftA, in_D5, h2, PS_oSx, PS_iGw, dv_cons,
      dv_nil, mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  have hM : ((g.pCore.edgeIdx x .minus false).map fun j => T1 PF D e ω
      ⟨(PS_iBaseM x g.pCore i₁ e₁ j).map (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)),
        cm * cmb * g.pCore.coeff⟩ s).sum +
      ((g.pCore.edgeIdx x .minus false).map fun j => T1 PF D e ω
      ⟨(PS_iBaseM x g.pCore i₁ e₁ j ++ [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]).map
        (rl (liftA 1 x)) ++ g.pEnv.map (Comp.map (liftA 1)), cm * g.pCore.coeff⟩ s).sum =
      pv (D ω) (Sum.elim e s) g.pEnv * ((g.pCore.edgeIdx x .minus false).map fun j => ∑ α,
        msc A.z * g.pCore.coeff.eval (msc A.z) *
        (dv (D ω) (Sum.elim e s) g.pCore.comps * (A.S (Sum.elim e s x) α : ℂ)) *
        PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s)
          (eraseIdxs [i₁, j] g.pCore.comps) * (A.G ω' (Sum.elim e s e₁.x) α *
            star (A.G ω' (Sum.elim e s (g.pCore.comps.getD j e₁).x) α)) *
          star (A.G ω' (Sum.elim e s x) (Sum.elim e s x))) ω).sum := by
    rw [← List.sum_map_add, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    rw [PBMi A x g i₁ e₁ e ω hp j s, hdj j hj]
  have hL3 := PBL A x g e ω hp s
  have hE1 := PBE1i A x g i₁ e₁ e ω hp (is₂.isEmpty = true) is₂.length
    (fun h => by simpa using h) s
  rw [hdE] at hE1
  have hD := (PBD A x g e ω _ hUD s).trans (congrArg _ (congrArg List.sum (List.map_congr_left
    fun d hd => Finset.sum_congr rfl fun α _ => by rw [hdD d hd α])))
  have hT0 : T0 PF D e ω g s = g.pCore.coeff.eval (msc A.z) *
      dv (D ω) (Sum.elim e s) g.pCore.comps * pv (D ω) (Sum.elim e s) g.pEnv *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) g.pCore.comps) ω := by
    rw [T0, termR_pform A hlab hp.labRand, m_eq A]
    rfl
  have hcore := in_core A hpl hIP hL hX (Sum.elim e s) (fun α => Sum.elim e (Fin.append s ![α]))
    (fun α => elim_append_comp_liftA e s ![α]) (fun α => by simp) ω
  rw [Q_apply'] at hcore
  linear_combination hM + hL3 + hE1 + hD - hT0 - pv (D ω) (Sum.elim e s) g.pEnv * hcore

end ValueEIn

/-! ## The value of [II, (4.24)] inside `P_x`, all cases -/

section ValueE

variable {k n : ℕ}

theorem mkC_ub {V : Type*} (κ : Kind) (u v : V) (hκ : ∀ ch, κ ≠ .inv ch)
    (hκ' : ∀ ch d, κ ≠ .wD ch d) : (mkC κ u v).label = none ∧ basB (mkC κ u v) = true := by
  refine ⟨rfl, ?_⟩
  unfold basB
  cases κ with
  | inv ch => exact absurd rfl (hκ ch)
  | wD ch d => exact absurd rfl (hκ' ch d)
  | _ => rfl

theorem dPieces_ub {V : Type*} [DecidableEq V] {p q : V} {c : Comp V}
    {ps : List (Comp V)} (h : c.dPieces p q = some ps) :
    ∀ c' ∈ ps, c'.label = none ∧ basB c' = true := by
  rcases c with ⟨κ, a, b, mi, l⟩
  intro c' hc'
  cases κ with
  | G ch => cases ch <;> simp [Comp.dPieces] at h <;> subst h <;> simp at hc' <;>
      rcases hc' with rfl | rfl <;> exact (basB_solidC _ _ _).symm
  | weight ch => cases ch <;> simp [Comp.dPieces] at h <;> subst h <;> simp at hc' <;>
      rcases hc' with rfl | rfl <;> exact (basB_solidC _ _ _).symm
  | light ch => cases ch <;> simp [Comp.dPieces] at h <;> subst h <;> simp at hc' <;>
      rcases hc' with rfl | rfl <;> exact (basB_solidC _ _ _).symm
  | _ => simp [Comp.dPieces] at h

theorem ShapeE.ub {x : Atom k n} {H : List (Comp (Atom k n))}
    {cs : List (Comp (Atom k (n + 1)))} (h : ShapeE x H cs)
    (hH : ∀ c ∈ H, c.label = none ∧ basB c = true) :
    ∀ c ∈ cs, c.label = none ∧ basB c = true := by
  have hl : ∀ B : List (Comp (Atom k n)), (∀ c ∈ B, c ∈ H) → ∀ c ∈ liftCs 1 B,
      c.label = none ∧ basB c = true := by
    intro B hB c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    obtain ⟨h1, h2⟩ := hH c' (hB c' hc')
    exact ⟨by simp [Comp.map, h1], by rw [basB_map]; exact h2⟩
  have hsx : (mkC (.waved .s) (liftA 1 x) (newA 0)).label = none ∧
      basB (mkC (.waved .s) (liftA 1 x) (newA 0)) = true := mkC_ub _ _ _ (by simp) (by simp)
  have hNew : ∀ {u : Atom k n} {κ : Kind} {a : Comp (Atom k (n + 1))}, κ.isSolid = true →
      NewH u κ a → a.label = none ∧ basB a = true := by
    intro u κ a hκ ha
    obtain ⟨ch, rfl⟩ := Kind.isSolid_iff.1 hκ
    rcases ha with rfl | rfl <;> exact mkC_ub _ _ _ (by simp) (by simp)
  rcases h with ⟨r₁, r₂, B, u₁, u₂, a₁, a₂, X, hB, hr₁, hr₂, ha₁, ha₂, hX, hXl, rfl⟩ |
    ⟨r₁, B, u₁, a₁, b, ch, hB, hr₁, ha₁, hb, hcs⟩ | ⟨ch, rfl⟩ |
    ⟨r, c, B, z, p, q, ps, e₀, hB, hr, hc, hcx, hpq, hps, he, rfl⟩
  · intro c hc
    rcases List.mem_append.1 hc with h' | h'
    · exact hl B (fun c hc => hB.symm.subset (List.mem_append_right _ hc)) c h'
    · rcases List.mem_append.1 h' with h' | h'
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h'
        rcases h' with rfl | rfl | rfl
        · exact hsx
        · exact hNew hr₁.1 ha₁
        · exact hNew hr₂.1 ha₂
      · obtain ⟨ch, rfl⟩ := hX c h'
        exact mkC_ub _ _ _ (by simp) (by simp)
  · intro c hc
    rcases hcs with rfl | rfl <;> rcases List.mem_append.1 hc with h' | h'
    · exact hl B (fun c hc => hB.symm.subset (List.mem_append_right _ hc)) c h'
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h'
      rcases h' with rfl | rfl | rfl
      · exact hsx
      · exact hNew hr₁.1 ha₁
      · exact hNew rfl hb
    · exact hl B (fun c hc => hB.symm.subset (List.mem_append_right _ hc)) c h'
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h'
      rcases h' with rfl | rfl | rfl
      · exact hsx
      · exact hNew rfl hb
      · exact hNew hr₁.1 ha₁
  · intro c hc
    rcases List.mem_append.1 hc with h' | h'
    · exact hl H (fun c hc => hc) c h'
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h'
      rcases h' with rfl | rfl
      · exact hsx
      · exact mkC_ub _ _ _ (by simp) (by simp)
  · intro c' hc'
    rcases List.mem_append.1 hc' with h' | h'
    · exact hl B (fun c hc => hB.symm.subset (List.mem_append_right _ hc)) c' h'
    · rcases List.mem_append.1 h' with h' | h'
      · exact dPieces_ub hps c' h'
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h'
        rcases h' with rfl | rfl
        · exact hsx
        · exact hNew hr.1 he

theorem ok_pLiftT' {x : Atom k n} {g : Graph k n} {E : TExpansion k n}
    (hE : ∀ s ∈ E, (∃ c ∈ s.g.comps, c.label = some (.Q, s.f x)) ∨
      ∀ c ∈ s.g.comps, c.label = none ∧ basB c = true) :
    ∀ t ∈ pLiftT x g E, OK t.g.comps := by
  intro t ht
  obtain ⟨s, hs, hq, rfl⟩ := mem_pLiftT.1 ht
  rcases hE s hs with ⟨c, hc, hl⟩ | hE'
  · exfalso
    have := List.any_eq_false.1 hq c hc
    simp [hl] at this
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    obtain ⟨hl, hb⟩ := hE' d hd
    unfold rl
    split_ifs with hr
    · exact Or.inr ⟨hr, by simpa [basB] using hb⟩
    · exact Or.inl hl
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    left
    simp [Comp.map, pEnv_unl g d hd]

/-- The value of `Ô^{(x)}_multi-e` applied to `𝒢` inside `P_x`. -/
theorem valueE {x : Atom k n} {g : Graph k n}
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.P, x)) (hp : g.Plain)
    (hNL : ∀ c ∈ g.comps, c.kind.isSolid = true → c.x ≠ c.y)
    {E : TExpansion k n} (hE : multiEHat x g.pCore = some E) :
    TExpansion.ValueEq (pLiftT x g E) g modelAdm := by
  have hub : ∀ c ∈ g.conj.pCore.comps, c.label = none ∧ basB c = true := fun c hc =>
    ⟨pCore_unl _ c hc, pCore_basB hp.conj c hc⟩
  have hNL' : ∀ c ∈ g.conj.pCore.comps, c.kind.isSolid = true → c.x ≠ c.y := by
    intro c hc hs
    obtain ⟨d, hd, -, rfl⟩ := pCore_mem hc
    rw [Graph.conj_comps'] at hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    exact hNL d' hd' (by simpa [conjC, Kind.conj_isSolid'] using hs)
  unfold multiEHat at hE
  split_ifs at hE with h1 h2 h3 h4
  · exact valueEOut_plain hlab hp hE
  · obtain ⟨E', hE', rfl⟩ := Option.map_eq_some_iff.1 hE
    rw [pLiftT_conj]
    refine valueEq_conj ?_ (okP hlab hp) ?_
    · refine valueEOut_plain (lab_conj hlab) hp.conj ?_
      rw [pCore_conj]; exact hE'
    · refine ok_pLiftT' fun s hs => ?_
      rcases shapesOut hNL' (by rw [pCore_conj]; exact hE') s hs with hq | ⟨cs, co, rfl, hsh⟩
      · exact Or.inl hq
      · exact Or.inr (hsh.ub hub)
  · exact valueEIn_plain hlab hp hE
  · obtain ⟨E', hE', rfl⟩ := Option.map_eq_some_iff.1 hE
    rw [pLiftT_conj]
    refine valueEq_conj ?_ (okP hlab hp) ?_
    · refine valueEIn_plain (lab_conj hlab) hp.conj ?_
      rw [pCore_conj]; exact hE'
    · refine ok_pLiftT' fun s hs => ?_
      have hout : ∀ ch, g.conj.pCore.edgeIdx x ch true = [] := by
        intro ch
        simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, not_not] at h1 h2
        rw [pCore_conj, psteps_edgeIdx_conj]
        cases ch
        · exact h2
        · exact h1
      rcases shapesIn hNL' hout (by rw [pCore_conj]; exact hE') s hs with hq | ⟨cs, co, rfl, hsh⟩
      · exact Or.inl hq
      · exact Or.inr (hsh.ub hub)

end ValueE

/-! ## One round: an identity inside `P_x`, the normalization and the labelled components moved
to `x` -/

section Round

variable {k : ℕ}

theorem PStepsTermOK.mono {n C C' : ℕ} {x : Atom k n} {g : Graph k n} {t : Tracked k n}
    (h : PStepsTermOK C x g t) (hC : C ≤ C') : PStepsTermOK C' x g t :=
  { h with nn := h.nn.mono hC, bnd := h.bnd.trans hC }

theorem St.mono {n C C' : ℕ} {x : Atom k n} {g : Graph k n} (h : St C x g) (hC : C ≤ C') :
    St C' x g :=
  { h with nn := h.nn.mono hC }

theorem sum_map_le {α : Type*} (L : List α) (f : α → ℕ) (b : ℕ) (h : ∀ a ∈ L, f a ≤ b) :
    (L.map f).sum ≤ b * L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := h a (List.mem_cons_self ..)
    have := ih fun a' ha' => h a' (List.mem_cons_of_mem _ ha')
    nlinarith

open Classical in
theorem Graph.viol_le {n : ℕ} (g : Graph k n) (x : Atom k n) :
    g.viol x ≤ 2 * g.comps.length := by
  unfold Graph.viol
  refine sum_map_le _ _ 2 fun c _ => ?_
  unfold vP
  split_ifs <;> omega

open Classical in
private theorem wBP_le4 {n : ℕ} (B : Atom k n → Prop) (c : Comp (Atom k n)) : wBP B c ≤ 4 := by
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ <;> simp only [wBP] <;> (try split_ifs) <;> omega

theorem Graph.pw_le {n : ℕ} (g : Graph k n) (x : Atom k n) :
    g.pw x ≤ 4 * g.comps.length := by
  unfold Graph.pw
  exact sum_map_le _ _ 4 fun c _ => wBP_le4 _ c

end Round

/-! ## The choice of the identity inside `P_x` -/

section OpTerms

variable {k : ℕ}

/-- Every solid edge has a `×`-dotted edge between its two atoms. -/
def XP {n : ℕ} (h : Graph k n) : Prop :=
  ∀ c ∈ h.comps, c.kind.isSolid = true → ∃ d ∈ h.comps, d.kind = .xdot ∧
    ((d.x = c.x ∧ d.y = c.y) ∨ (d.x = c.y ∧ d.y = c.x))

theorem xdotsAt_of_XP {n : ℕ} {x : Atom k n} {h : Graph k n} (hXP : XP h)
    {is : List ℕ} (his : ∀ j ∈ is, ∃ hj : j < h.comps.length, h.comps[j].kind.isSolid = true ∧
      (h.comps[j].x = x ∨ h.comps[j].y = x)) : h.xdotsAt x is = true := by
  unfold Graph.xdotsAt
  rw [List.all_eq_true]
  intro j hj
  obtain ⟨hjl, hs, hx⟩ := his j hj
  rw [List.getElem?_eq_getElem hjl]
  simp only
  obtain ⟨d, hd, hdk, hdp⟩ := hXP _ (List.getElem_mem hjl) hs
  unfold Graph.hasXdot
  rw [List.any_eq_true]
  refine ⟨d, hd, ?_⟩
  by_cases hcx : h.comps[j].x = x
  · simp only [hcx, beq_self_eq_true, ite_true, hdk, beq_self_eq_true, Bool.true_and]
    rcases hdp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2, hcx]
    · simp [h1, h2, hcx]
  · have hcy : h.comps[j].y = x := hx.resolve_left hcx
    simp only [hdk, beq_self_eq_true, Bool.true_and]
    rw [if_neg (by simpa using hcx)]
    rcases hdp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2, hcy]
    · simp [h1, h2, hcy]

theorem ep_solid_at {n : ℕ} {x : Atom k n} {h : Graph k n} {ch : Charge} {out : Bool}
    {j : ℕ} (hj : j ∈ h.edgeIdx x ch out) : ∃ hjl : j < h.comps.length,
      h.comps[j].kind.isSolid = true ∧ (h.comps[j].x = x ∨ h.comps[j].y = x) := by
  obtain ⟨hjl, hep⟩ := edgeIdx_mem hj
  obtain ⟨hk, ho, hi⟩ := ep_spec x hep
  refine ⟨hjl, by simp only at hk; rw [hk]; rfl, ?_⟩
  cases out
  · exact Or.inr (hi rfl).1
  · exact Or.inl (ho rfl).1

theorem multiEOut_isSome {n : ℕ} {x : Atom k n} {h : Graph k n} (hXP : XP h)
    (hne : h.edgeIdx x .plus true ≠ []) : ∃ E, multiEOut x h = some E := by
  have hX : h.xdotsAt x (h.edgeIdx x .plus true ++ h.edgeIdx x .minus true ++
      h.edgeIdx x .plus false ++ h.edgeIdx x .minus false) = true := by
    refine xdotsAt_of_XP hXP fun j hj => ?_
    simp only [List.mem_append] at hj
    rcases hj with ((hj | hj) | hj) | hj <;> exact ep_solid_at hj
  unfold multiEOut
  rcases hOP : h.edgeIdx x .plus true with _ | ⟨i₁, is₂⟩
  · exact absurd hOP hne
  obtain ⟨hi, -⟩ := edgeIdx_mem (show i₁ ∈ h.edgeIdx x .plus true by rw [hOP]; simp)
  rw [hOP] at hX
  simp only [List.getElem?_eq_getElem hi]
  rw [if_neg (by rw [hX]; simp)]
  exact ⟨_, rfl⟩

theorem multiEIn_isSome {n : ℕ} {x : Atom k n} {h : Graph k n} (hXP : XP h)
    (hne : h.edgeIdx x .plus false ≠ []) : ∃ E, multiEIn x h = some E := by
  have hX : h.xdotsAt x (h.edgeIdx x .plus false ++ h.edgeIdx x .minus false) = true := by
    refine xdotsAt_of_XP hXP fun j hj => ?_
    simp only [List.mem_append] at hj
    rcases hj with hj | hj <;> exact ep_solid_at hj
  unfold multiEIn
  rcases hIP : h.edgeIdx x .plus false with _ | ⟨i₁, is₂⟩
  · exact absurd hIP hne
  obtain ⟨hi, -⟩ := edgeIdx_mem (show i₁ ∈ h.edgeIdx x .plus false by rw [hIP]; simp)
  rw [hIP] at hX
  simp only [List.getElem?_eq_getElem hi]
  rw [if_neg (by rw [hX]; simp)]
  exact ⟨_, rfl⟩

theorem XP.conj {n : ℕ} {h : Graph k n} (hXP : XP h) : XP h.conj := by
  intro c hc hs
  rw [Graph.conj_comps'] at hc ⊢
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  obtain ⟨d, hd, hdk, hdp⟩ := hXP c' hc' (by simpa [conjC, Kind.conj_isSolid'] using hs)
  exact ⟨conjC d, List.mem_map_of_mem hd, by simp [conjC, hdk, Kind.conj], hdp⟩

theorem multiEHat_isSome {n : ℕ} {x : Atom k n} {h : Graph k n} (hXP : XP h)
    (hne : ∃ ch out, h.edgeIdx x ch out ≠ []) : ∃ E, multiEHat x h = some E := by
  unfold multiEHat
  split_ifs with h1 h2 h3 h4
  · exact multiEOut_isSome hXP (by simpa using h1)
  · obtain ⟨E, hE⟩ := multiEOut_isSome hXP.conj (by rw [psteps_edgeIdx_conj]; simpa [Charge.flip] using h2)
    exact ⟨_, by rw [hE]; rfl⟩
  · exact multiEIn_isSome hXP (by simpa using h3)
  · obtain ⟨E, hE⟩ := multiEIn_isSome hXP.conj (by rw [psteps_edgeIdx_conj]; simpa [Charge.flip] using h4)
    exact ⟨_, by rw [hE]; rfl⟩
  · exfalso
    obtain ⟨ch, out, hne⟩ := hne
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, not_not] at h1 h2 h3 h4
    cases ch <;> cases out <;> simp_all

theorem XP_core {n C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g) :
    XP g.pCore := by
  intro c hc hs
  obtain ⟨d, hd, -, rfl⟩ := pCore_mem hc
  have hp : g.partB d = true := by
    by_contra hp
    have : d ∈ g.unpart := Graph.mem_unpart.2 ⟨hd, hs, by simpa using hp⟩
    rw [hS.unp] at this; simp at this
  obtain ⟨e, he, hek, hep⟩ := (g.partB_iff d).1 hp
  have hel : e.label = none := by
    by_contra hne
    have := hS.nn.plain.labRand e he (Option.isSome_iff_ne_none.2 hne)
    rw [hek] at this; simp [Kind.isRandom] at this
  refine ⟨{ e with label := none }, ?_, hek, hep⟩
  rw [pCore_comps]
  exact List.mem_map_of_mem (List.mem_filter.2 ⟨he, by simp [coreP, hek, Kind.isRandom]⟩)

end OpTerms

section OpLengths

variable {k : ℕ}

theorem length_pLiftT_le {n : ℕ} (x : Atom k n) (g : Graph k n) (E : TExpansion k n) :
    (pLiftT x g E).length ≤ E.length := List.length_filterMap_le _ _

theorem splitRegular_length_le {V : Type*} [DecidableEq V] (x : V) (cs : List (Comp V)) :
    (splitRegular x cs).length ≤ 2 ^ cs.length := by
  induction cs with
  | nil => simp [splitRegular]
  | cons c cs ih =>
    rcases c with ⟨κ, a, b, mi, l⟩
    cases κ <;> simp only [splitRegular] <;> (try split_ifs) <;>
      simp only [List.length_append, List.length_map, List.length_cons, pow_succ] <;> omega

theorem dTerms_length_le {V : Type*} [DecidableEq V] (p q : V) (cs : List (Comp V)) :
    (dTerms p q cs).length ≤ cs.length :=
  (List.length_filterMap_le _ _).trans (by simp)

theorem edgeIdx_length_le {n : ℕ} (h : Graph k n) (x : Atom k n) (ch : Charge)
    (out : Bool) : (h.edgeIdx x ch out).length ≤ h.comps.length := by
  unfold Graph.edgeIdx
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem pCore_length_le {n : ℕ} (g : Graph k n) : g.pCore.comps.length ≤ g.comps.length := by
  rw [pCore_comps, List.length_map]; exact List.length_filter_le _ _

theorem eraseIdxs_length_le {α : Type*} (is : List ℕ) (l : List α) :
    (eraseIdxs is l).length ≤ l.length := by
  unfold eraseIdxs
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem oWeightP2Pos_length {n : ℕ} {x : Atom k n} {h : Graph k n} {E : TExpansion k n}
    (hE : oWeightP2Pos x h = some E) : E.length ≤ h.comps.length + 2 := by
  unfold oWeightP2Pos at hE
  split at hE
  · cases hE
  rename_i i _
  simp only [Option.some.injEq] at hE
  subst hE
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map]
  have := dTerms_length_le (newA 0) (liftA 1 x) (liftCs 1 (h.comps.eraseIdx i))
  have h2 : (liftCs 1 (h.comps.eraseIdx i)).length ≤ h.comps.length := by
    simp only [liftCs, List.length_map, List.length_eraseIdx]
    split_ifs <;> omega
  omega

theorem oWeightP2T_length {n : ℕ} (x : Atom k n) (g : Graph k n) :
    (oWeightP2T x g).length ≤ g.comps.length + 2 := by
  have hc := pCore_length_le g
  unfold oWeightP2T
  rcases hE : oWeightP2Pos x g.pCore with _ | E
  · dsimp only
    rcases hE' : oWeightP2Pos x g.pCore.conj with _ | E'
    · simp [Tracked.self]
    · dsimp only
      refine (length_pLiftT_le _ _ _).trans ?_
      have := oWeightP2Pos_length hE'
      simp only [TExpansion.conj, List.length_map, Graph.conj_comps'] at this ⊢
      omega
  · dsimp only
    have := oWeightP2Pos_length hE
    exact (length_pLiftT_le _ _ _).trans (by omega)

theorem oOut_length {n : ℕ} (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ)
    (e₁ : Comp (Atom k n)) : (psteps_oOut x Γ i₁ is₂ e₁).length ≤ 8 * Γ.comps.length + 8 := by
  have h1 := edgeIdx_length_le Γ x .minus true
  have h2 := edgeIdx_length_le Γ x .plus false
  have h3 : (PS_oDs x Γ i₁ e₁).length ≤ Γ.comps.length := by
    unfold PS_oDs
    rw [List.length_map]
    refine (dTerms_length_le _ _ _).trans ?_
    simp only [liftCs, List.length_map]
    exact eraseIdxs_length_le _ _
  unfold psteps_oOut
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  split_ifs <;> simp only [List.length_nil, List.length_cons] <;> omega

theorem iOut_length {n : ℕ} (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ)
    (e₁ : Comp (Atom k n)) : (psteps_iOut x Γ i₁ is₂ e₁).length ≤ 8 * Γ.comps.length + 8 := by
  have h1 := edgeIdx_length_le Γ x .minus false
  have h3 : (PS_iDs x Γ i₁ e₁).length ≤ Γ.comps.length := by
    unfold PS_iDs
    rw [List.length_map]
    refine (dTerms_length_le _ _ _).trans ?_
    simp only [liftCs, List.length_map]
    exact eraseIdxs_length_le _ _
  unfold psteps_iOut
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  split_ifs <;> simp only [List.length_nil, List.length_cons] <;> omega

theorem multiEHat_length {n : ℕ} {x : Atom k n} {h : Graph k n} {E : TExpansion k n}
    (hE : multiEHat x h = some E) : E.length ≤ 8 * h.comps.length + 8 := by
  unfold multiEHat at hE
  split_ifs at hE
  · obtain ⟨i₁, is₂, e₁, -, -, -, hEq⟩ := multiEOut_some x h hE
    rw [hEq]
    exact oOut_length x h i₁ is₂ e₁
  · obtain ⟨E', hE', hEq⟩ := Option.map_eq_some_iff.1 hE
    obtain ⟨i₁, is₂, e₁, -, -, -, hEq'⟩ := multiEOut_some x h.conj hE'
    rw [← hEq, hEq']
    have := oOut_length x h.conj i₁ is₂ e₁
    rw [TExpansion.conj, List.length_map]
    rw [Graph.conj_comps', List.length_map] at this
    exact this
  · obtain ⟨i₁, is₂, e₁, -, -, -, hEq⟩ := multiEIn_some x h hE
    rw [hEq]
    exact iOut_length x h i₁ is₂ e₁
  · obtain ⟨E', hE', hEq⟩ := Option.map_eq_some_iff.1 hE
    obtain ⟨i₁, is₂, e₁, -, -, -, hEq'⟩ := multiEIn_some x h.conj hE'
    rw [← hEq, hEq']
    have := iOut_length x h.conj i₁ is₂ e₁
    rw [TExpansion.conj, List.length_map]
    rw [Graph.conj_comps', List.length_map] at this
    exact this

end OpLengths

section RoundFull

variable {k : ℕ}

end RoundFull

section Iter

variable {k : ℕ}

end Iter

section InitMerge

variable {k n : ℕ}

end InitMerge

/-! ## [II, Lemma 4.13] -/

section Main

variable {k : ℕ}

/-- No weighted labelled weight or edge end at the block of `y`: no labelled weight or solid edge
is attached to that block. -/
theorem labelledFree_of_pw {n : ℕ} {g : Graph k n} {y : Atom k n} (hp : g.Plain)
    (h : g.pw y = 0) : g.LabelledFreeAtBlock y := by
  classical
  intro c hc hl hr
  unfold Graph.pw at h
  have h0 : wBP (fun u => g.SameBlock u y) c = 0 :=
    List.sum_eq_zero_iff.1 h _ (List.mem_map_of_mem hc)
  obtain ⟨-, hinv, hwD, -, hwf, -⟩ := hp c hc
  rcases hk : c.kind with ch | ch | ch | ch | ⟨ch, d⟩ | w | o | ⟨a, b⟩ | _ | ⟨j, r, b⟩ | _ | _
  · rw [wBP_G hk hl] at h0
    by_cases h1 : g.SameBlock c.x y <;> by_cases h2 : g.SameBlock c.y y <;> simp_all
  · rw [wBP_W hk hl] at h0
    have hy : c.y = c.x := hwf (by rw [hk]; rfl)
    by_cases h1 : g.SameBlock c.x y
    · simp [h1] at h0
    · exact ⟨h1, by rw [hy]; exact h1⟩
  · rw [wBP_L hk hl] at h0
    have hy : c.y = c.x := hwf (by rw [hk]; rfl)
    by_cases h1 : g.SameBlock c.x y
    · simp [h1] at h0
    · exact ⟨h1, by rw [hy]; exact h1⟩
  · exact absurd hk (hinv ch)
  · exact absurd hk (hwD ch d)
  all_goals (rw [hk] at hr; simp [Kind.isRandom] at hr)

end Main

/-! ## The components at an external atom -/

section OAt

variable {k : ℕ}

/-- The component has an end at the external atom `o`. -/
def atO {n : ℕ} (o : Fin k) (c : Comp (Atom k n)) : Bool :=
  decide (c.x = .inl o ∨ c.y = .inl o)

/-- Every component of `Γ` at the external atom `o` is a diffusive edge. -/
def ODiff {n : ℕ} (o : Fin k) (Γ : Graph k n) : Prop :=
  ∀ c ∈ Γ.comps, (c.x = .inl o ∨ c.y = .inl o) → c.kind.isDiffusive = true

/-- The components of `T` at the external atom `o` are, up to order, those of `Γ`. -/
def OKeep {n : ℕ} (o : Fin k) (Γ T : Graph k n) : Prop :=
  (T.comps.filter (atO o)).Perm (Γ.comps.filter (atO o))

/-- The components of the output graph `t` at the external atom `o` are, up to order, the images
of those of `Γ`. -/
def OOut {n : ℕ} (o : Fin k) (Γ : Graph k n) (t : Tracked k n) : Prop :=
  (t.g.comps.filter (atO o)).Perm ((Γ.comps.filter (atO o)).map (Comp.map t.f))

/-- At every external atom at which all components of `Γ` are diffusive, the components of `T`
are, up to order, those of `Γ`. -/
def PStepsOK1 {n : ℕ} (Γ T : Graph k n) : Prop := ∀ o, ODiff o Γ → OKeep o Γ T

/-- At every external atom at which all components of `Γ` are diffusive, the components of the
output graph `t` are, up to order, the images of those of `Γ`. -/
def OO1 {n : ℕ} (Γ : Graph k n) (t : Tracked k n) : Prop := ∀ o, ODiff o Γ → OOut o Γ t

theorem psteps_atO_iff {n : ℕ} {o : Fin k} {c : Comp (Atom k n)} :
    atO o c = true ↔ (c.x = .inl o ∨ c.y = .inl o) := by
  simp [atO]

theorem ODiff.diff {n : ℕ} {o : Fin k} {Γ : Graph k n} (hO : ODiff o Γ)
    {c : Comp (Atom k n)} (hc : c ∈ Γ.comps) (ho : atO o c = true) : c.kind.isDiffusive = true :=
  hO c hc (psteps_atO_iff.1 ho)

/-- A random component of a graph with only diffusive components at `o` is not at `o`. -/
theorem ODiff.random {n : ℕ} {o : Fin k} {Γ : Graph k n} (hO : ODiff o Γ)
    {c : Comp (Atom k n)} (hc : c ∈ Γ.comps) (hr : c.kind.isRandom = true) : atO o c = false := by
  cases ho : atO o c
  · rfl
  · have := hO.diff hc ho
    rw [Kind.not_isDiffusive_of_isRandom hr] at this
    cases this

theorem OKeep.diff {n : ℕ} {o : Fin k} {Γ T : Graph k n} (h : OKeep o Γ T)
    (hO : ODiff o Γ) {c : Comp (Atom k n)} (hc : c ∈ T.comps) (ho : atO o c = true) :
    c.kind.isDiffusive = true :=
  hO.diff (List.mem_filter.1 (h.subset (List.mem_filter.2 ⟨hc, ho⟩))).1 ho

theorem ODiff.of_keep {n : ℕ} {o : Fin k} {Γ T : Graph k n} (h : OKeep o Γ T)
    (hO : ODiff o Γ) : ODiff o T :=
  fun _ hc ho => h.diff hO hc (psteps_atO_iff.2 ho)

theorem OKeep.atO_false {n : ℕ} {o : Fin k} {Γ T : Graph k n} (h : OKeep o Γ T)
    (hO : ODiff o Γ) {c : Comp (Atom k n)} (hc : c ∈ T.comps) (hd : c.kind.isDiffusive = false) :
    atO o c = false := by
  cases ho : atO o c
  · rfl
  · rw [h.diff hO hc ho] at hd
    cases hd

theorem OKeep.erase {n : ℕ} {o : Fin k} {Γ T : Graph k n} (h : OKeep o Γ T) {i : ℕ}
    {c : Comp (Atom k n)} (hc : T.comps[i]? = some c) (hco : atO o c = false) (co : Coeff) :
    OKeep o Γ ⟨T.comps.eraseIdx i, co⟩ := by
  have hp := (perm_cons_eraseIdx hc).filter (atO o)
  rw [List.filter_cons_of_neg (by simp [hco])] at hp
  exact hp.symm.trans h

theorem OKeep.append {n : ℕ} {o : Fin k} {Γ : Graph k n} {L : List (Comp (Atom k n))}
    (h : (L.filter (atO o)).Perm (Γ.comps.filter (atO o))) (new : List (Comp (Atom k n)))
    (hnew : ∀ d ∈ new, atO o d = false) (co : Coeff) : OKeep o Γ ⟨L ++ new, co⟩ := by
  have : new.filter (atO o) = [] := List.filter_eq_nil_iff.2 fun d hd => by simp [hnew d hd]
  change ((L ++ new).filter (atO o)).Perm _
  rw [List.filter_append, this, List.append_nil]
  exact h

private theorem Comp.map_id'' {V : Type*} (c : Comp V) : c.map id = c := by
  cases c; simp [Comp.map]

private theorem Comp.map_comp'' {U V W : Type*} (f : U → V) (g : V → W) (c : Comp U) :
    (c.map f).map g = c.map (g ∘ f) := by
  rcases c with ⟨κ, a, b, mi, l⟩
  rcases l with _ | ⟨pq, u⟩ <;> simp [Comp.map, List.map_map, Function.comp_def]

/-- Components mapped by an atom map that sends only `o` to `o`: those at `o` are the images of
those at `o`. -/
theorem filter_atO_map {n m : ℕ} {o : Fin k} (f : Atom k n → Atom k m)
    (hf : ∀ u, f u = .inl o ↔ u = .inl o) (L : List (Comp (Atom k n))) :
    (L.map (Comp.map f)).filter (atO o) = (L.filter (atO o)).map (Comp.map f) := by
  rw [List.filter_map]
  congr 1
  refine List.filter_congr fun c _ => ?_
  simp only [Function.comp_apply, atO, Comp.map, hf]

theorem atO_map {n m : ℕ} {o : Fin k} {f : Atom k n → Atom k m}
    (hf : ∀ u, f u = .inl o ↔ u = .inl o) (c : Comp (Atom k n)) : atO o (c.map f) = atO o c := by
  simp only [atO, Comp.map, hf]

theorem liftA_iff {n : ℕ} (o : Fin k) (u : Atom k n) :
    liftA 1 u = .inl o ↔ u = .inl o := by
  rcases u with a | a <;> simp [liftA]

theorem OOut.self {n : ℕ} (o : Fin k) (Γ : Graph k n) : OOut o Γ (Tracked.self Γ) := by
  unfold OOut
  have : (Γ.comps.filter (atO o)).map (Comp.map (Tracked.self Γ).f) = Γ.comps.filter (atO o) := by
    conv_rhs => rw [← List.map_id (Γ.comps.filter (atO o))]
    exact List.map_congr_left fun c _ => Comp.map_id'' c
  rw [this]
  exact List.Perm.refl _

theorem PStepsOK1.refl {n : ℕ} (Γ : Graph k n) : PStepsOK1 Γ Γ := fun _ _ => List.Perm.refl _

theorem OO1.self {n : ℕ} (Γ : Graph k n) : OO1 Γ (Tracked.self Γ) :=
  fun o _ => OOut.self o Γ

theorem PStepsOK1.trans {n : ℕ} {Γ T T' : Graph k n} (h1 : PStepsOK1 Γ T) (h2 : PStepsOK1 T T') :
    PStepsOK1 Γ T' := fun o hO => (h2 o (ODiff.of_keep (h1 o hO) hO)).trans (h1 o hO)

/-- The graph `T` itself as an output keeps the components at the external atoms. -/
theorem OO1.of_keep {n : ℕ} {Γ T : Graph k n} (h : PStepsOK1 Γ T) : OO1 Γ (Tracked.self T) := by
  intro o hO
  have hid : (Γ.comps.filter (atO o)).map (Comp.map (Tracked.self T).f) =
      Γ.comps.filter (atO o) := by
    conv_rhs => rw [← List.map_id (Γ.comps.filter (atO o))]
    exact List.map_congr_left fun c _ => Comp.map_id'' c
  change (T.comps.filter (atO o)).Perm _
  rw [hid]
  exact h o hO

theorem OO1.of_ok {n : ℕ} {Γ T : Graph k n} {t : Tracked k n} (h1 : PStepsOK1 Γ T)
    (h2 : OO1 T t) : OO1 Γ t := by
  intro o hO
  have h1o := h1 o hO
  exact (h2 o (ODiff.of_keep h1o hO)).trans (List.Perm.map _ h1o)

theorem ODiff.of_oout {n : ℕ} {o : Fin k} {Γ : Graph k n} {t : Tracked k n}
    (h : OOut o Γ t) (hO : ODiff o Γ) : ODiff o t.g := by
  intro c hc ho
  have hc' : c ∈ (Γ.comps.filter (atO o)).map (Comp.map t.f) :=
    h.subset (List.mem_filter.2 ⟨hc, psteps_atO_iff.2 ho⟩)
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc'
  obtain ⟨hdΓ, hdo⟩ := List.mem_filter.1 hd
  exact hO.diff hdΓ hdo

theorem OOut.comp {n : ℕ} {o : Fin k} {Γ : Graph k n} {t : Tracked k n}
    {s : Tracked k t.nOut} (h1 : OOut o Γ t) (h2 : OOut o t.g s) :
    OOut o Γ (t.comp s) := by
  change (s.g.comps.filter (atO o)).Perm ((Γ.comps.filter (atO o)).map (Comp.map (s.f ∘ t.f)))
  refine h2.trans ?_
  refine (List.Perm.map _ h1).trans ?_
  rw [List.map_map]
  refine List.Perm.of_eq (List.map_congr_left fun c _ => ?_)
  exact Comp.map_comp'' t.f s.f c

theorem OO1.comp {n : ℕ} {Γ : Graph k n} {t : Tracked k n} {s : Tracked k t.nOut}
    (h1 : OO1 Γ t) (h2 : OO1 t.g s) : OO1 Γ (t.comp s) :=
  fun o hO => (h1 o hO).comp (h2 o (ODiff.of_oout (h1 o hO) hO))

/-- Removing a component that is not diffusive keeps the components at the external atoms. -/
theorem PStepsOK1.erase {n : ℕ} {Γ T : Graph k n} (h : PStepsOK1 Γ T) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hcd : c.kind.isDiffusive = false) (co : Coeff) :
    PStepsOK1 Γ ⟨T.comps.eraseIdx i, co⟩ := fun o hO =>
  (h o hO).erase hc ((h o hO).atO_false hO (List.mem_of_getElem? hc) hcd) co

/-- Adding components that are not at the external atoms at which all components of `Γ` are
diffusive keeps the components there. -/
theorem PStepsOK1.append {n : ℕ} {Γ T : Graph k n} (h : PStepsOK1 Γ T) (new : List (Comp (Atom k n)))
    (hnew : ∀ o, ODiff o Γ → ∀ d ∈ new, atO o d = false) (co : Coeff) :
    PStepsOK1 Γ ⟨T.comps ++ new, co⟩ := fun o hO => OKeep.append (h o hO) new (hnew o hO) co

/-- The components at `o` under `O_merge`, when `o` is the only atom with image `o` and every
component at `o` is diffusive. -/
theorem filter_atO_merge {n m : ℕ} (o : Fin k) (rep : Atom k n → Atom k n)
    (f : Atom k n → Atom k m) (hf : ∀ u, f u = .inl o ↔ u = .inl o) :
    ∀ L : List (Comp (Atom k n)), (∀ c ∈ L, atO o c = true → c.kind.isDiffusive = true) →
      (L.filterMap (psteps_mergeComp rep f)).filter (atO o) = (L.filter (atO o)).map (Comp.map f)
  | [], _ => rfl
  | c :: L, hL => by
    have ih := filter_atO_merge o rep f hf L fun d hd => hL d (List.mem_cons_of_mem _ hd)
    rw [List.filterMap_cons]
    by_cases ho : atO o c = true
    · have hdf := hL c (List.mem_cons_self ..) ho
      have hnd : c.kind ≠ .dot := fun h => by rw [h] at hdf; cases hdf
      have hns : c.kind.isSolid = false := by
        cases hk : c.kind <;> simp_all [Kind.isSolid, Kind.isDiffusive]
      rw [mergeComp_other hnd hns, List.filter_cons_of_pos ho]
      have ho' : atO o (c.map f) = true := by
        rw [psteps_atO_iff] at ho ⊢
        simp only [Comp.map]
        rcases ho with h | h
        · exact Or.inl ((hf _).2 h)
        · exact Or.inr ((hf _).2 h)
      rw [List.filter_cons_of_pos ho', ih, List.map_cons]
    · have ho2 : ¬ (c.x = .inl o ∨ c.y = .inl o) := fun h => ho (psteps_atO_iff.2 h)
      push Not at ho2
      obtain ⟨hx, hy⟩ := ho2
      have hx' : f c.x ≠ .inl o := fun h => hx ((hf _).1 h)
      have hy' : f c.y ≠ .inl o := fun h => hy ((hf _).1 h)
      rw [List.filter_cons_of_neg ho]
      rcases hm : psteps_mergeComp rep f c with _ | c'
      · exact ih
      · have hc' : atO o c' = false := by
          unfold psteps_mergeComp at hm
          split_ifs at hm
          · obtain rfl := Option.some.inj hm
            simp [atO, Comp.map, hx']
          · obtain rfl := Option.some.inj hm
            simp [atO, Comp.map, hx', hy']
        simp only
        rw [List.filter_cons_of_neg (by simp [hc']), ih]

/-- The atom map of `O_merge` sends only `o` to `o`. -/
theorem PStepsMergeSpec.f_iff {n : ℕ} {Γ : Graph k n} {t : Tracked k n} (hs : PStepsMergeSpec Γ t)
    (o : Fin k) (u : Atom k n) : t.f u = .inl o ↔ u = .inl o := by
  obtain ⟨φ, hφ, -⟩ := hs.f_inr
  rcases u with a | i
  · simp [hs.f_inl]
  · rw [hφ]
    simp

theorem filter_atO_nd {n : ℕ} {o : Fin k} {L : List (Comp (Atom k n))}
    (hL : ∀ c ∈ L, atO o c = true → c.kind ≠ .dot) :
    L.filter (atO o) = (L.filter fun c => decide (c.kind ≠ .dot)).filter (atO o) := by
  rw [List.filter_filter]
  refine List.filter_congr fun c hc => ?_
  by_cases ho : atO o c = true
  · simp [ho, hL c hc ho]
  · simp [ho]

/-- The output of `O_merge` followed by the removal of redundant dotted edges keeps the components
at `o`. -/
theorem merge_oout {n : ℕ} {o : Fin k} {Γ T : Graph k n} {t : Tracked k n}
    (hs : PStepsMergeSpec T t) (hO : ODiff o Γ) (hK : OKeep o Γ T) {g' : Graph k t.nOut}
    (hsub : g'.comps.Sublist t.g.comps)
    (hnd : (g'.comps.filter fun c => decide (c.kind ≠ .dot)).Perm
      (t.g.comps.filter fun c => decide (c.kind ≠ .dot))) :
    OOut o Γ ⟨t.nOut, g', t.f⟩ := by
  have hT : ∀ c ∈ T.comps, atO o c = true → c.kind.isDiffusive = true :=
    fun c hc ho => hK.diff hO hc ho
  have hm := filter_atO_merge o T.psteps_mrep t.f (hs.f_iff o) T.comps hT
  rw [← hs.comps_eq] at hm
  have hnd1 : ∀ c ∈ t.g.comps, atO o c = true → c.kind ≠ .dot := by
    intro c hc ho h
    have hc' : c ∈ (T.comps.filter (atO o)).map (Comp.map t.f) := by
      rw [← hm]
      exact List.mem_filter.2 ⟨hc, ho⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc'
    obtain ⟨hdT, hdo⟩ := List.mem_filter.1 hd
    have := hT d hdT hdo
    simp only [Comp.map] at h
    rw [h] at this
    cases this
  have hnd2 : ∀ c ∈ g'.comps, atO o c = true → c.kind ≠ .dot :=
    fun c hc ho => hnd1 c (hsub.subset hc) ho
  change (g'.comps.filter (atO o)).Perm ((Γ.comps.filter (atO o)).map (Comp.map t.f))
  rw [filter_atO_nd hnd2]
  refine (hnd.filter (atO o)).trans ?_
  rw [← filter_atO_nd hnd1, hm]
  exact List.Perm.map _ hK

end OAt

/-! ## The components at an external atom in the terms of the steps inside `P_x` -/

section OTerms

variable {k n : ℕ}

theorem rl_atO {m : ℕ} {o : Fin k} (y : Atom k m) (c : Comp (Atom k m)) :
    atO o (rl y c) = atO o c := by
  unfold rl
  split <;> rfl

theorem solidC_atO {m : ℕ} {o : Fin k} (ch : Charge) {u v : Atom k m}
    (hu : u ≠ .inl o) (hv : v ≠ .inl o) : atO o (solidC ch u v) = false := by
  unfold solidC
  split_ifs <;> simp [atO, mkC, hu, hv]

/-- The factors of `-∂_{h_{pq}}` of a component not at `o`, with `p, q ≠ o`, are not at `o`. -/
theorem dPieces_atO {m : ℕ} {o : Fin k} {p q : Atom k m} {c : Comp (Atom k m)}
    {ps : List (Comp (Atom k m))} (h : c.dPieces p q = some ps) (hp : p ≠ .inl o)
    (hq : q ≠ .inl o) (hc : atO o c = false) : ∀ a ∈ ps, atO o a = false := by
  have hcx : c.x ≠ .inl o := fun e => by simp [atO, e] at hc
  have hcy : c.y ≠ .inl o := fun e => by simp [atO, e] at hc
  have hb : (if c.kind.isWeight then c.x else c.y) ≠ .inl o := by
    split
    · exact hcx
    · exact hcy
  intro a ha
  rcases c with ⟨κ, cx, cy, mi, l⟩
  simp only at hcx hcy hb
  cases κ with
  | G ch =>
    cases ch <;> simp only [Comp.dPieces, Option.some.injEq] at h <;> subst h <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha <;>
      rcases ha with rfl | rfl <;> exact solidC_atO _ (by assumption) (by assumption)
  | weight ch =>
    cases ch <;> simp only [Comp.dPieces, Option.some.injEq] at h <;> subst h <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha <;>
      rcases ha with rfl | rfl <;> exact solidC_atO _ (by assumption) (by assumption)
  | light ch =>
    cases ch <;> simp only [Comp.dPieces, Option.some.injEq] at h <;> subst h <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha <;>
      rcases ha with rfl | rfl <;> exact solidC_atO _ (by assumption) (by assumption)
  | _ => simp [Comp.dPieces] at h

/-- The random components of `g.pCore` are not at an external atom at which all components of `g`
are diffusive. -/
theorem core_random {o : Fin k} {g : Graph k n} (hO : ODiff o g) {c : Comp (Atom k n)}
    (hc : c ∈ g.pCore.comps) (hr : c.kind.isRandom = true) : atO o c = false := by
  obtain ⟨d, hd, -, rfl⟩ := pCore_mem hc
  change atO o d = false
  exact hO.random hd hr

/-- The components of `g.pCore` at `o` are those of `g`. -/
theorem core_filter {o : Fin k} {g : Graph k n} (hO : ODiff o g) (hlr : g.LabRand) :
    g.pCore.comps.filter (atO o) = g.comps.filter (atO o) := by
  rw [pCore_comps]
  rw [show ((g.comps.filter coreP).map fun c => { c with label := none }).filter (atO o) =
      ((g.comps.filter coreP).filter (atO o)).map fun c => { c with label := none } by
    rw [List.filter_map]
    rfl]
  rw [List.filter_filter]
  have e1 : (g.comps.filter fun c => atO o c && coreP c) = g.comps.filter (atO o) := by
    refine List.filter_congr fun c hc => ?_
    by_cases ho : atO o c = true
    · have hd := hO.diff hc ho
      have hr : c.kind.isRandom = false := by
        cases hk : c.kind <;> simp_all [Kind.isRandom, Kind.isDiffusive]
      simp [ho, coreP, hr]
    · simp [ho]
  rw [e1]
  conv_rhs => rw [← List.map_id (g.comps.filter (atO o))]
  refine List.map_congr_left fun c hc => ?_
  obtain ⟨hcg, ho⟩ := List.mem_filter.1 hc
  have hd := hO.diff hcg ho
  have hl : c.label = none := by
    by_contra hne
    have hr := hlr c hcg (Option.isSome_iff_ne_none.2 hne)
    rw [Kind.not_isDiffusive_of_isRandom hr] at hd
    cases hd
  obtain ⟨κ, a, b, mi, l⟩ := c
  simp only at hl
  subst hl
  rfl

/-- A term `s` of an identity applied to `g.pCore` that keeps the components at `o`, read inside
`P_x` (`pLiftT`), keeps the components of `g` at `o`. -/
theorem pLift_oout {o : Fin k} {x : Atom k n} {g : Graph k n} (hO : ODiff o g)
    (hlr : g.LabRand) {s : Tracked k n} (hf : ∀ u, s.f u = .inl o ↔ u = .inl o)
    (hs : OOut o g.pCore s) :
    OOut o g ⟨s.nOut, ⟨s.g.comps.map (rl (s.f x)) ++ g.pEnv.map (Comp.map s.f), s.g.coeff⟩,
      s.f⟩ := by
  change ((s.g.comps.map (rl (s.f x)) ++ g.pEnv.map (Comp.map s.f)).filter (atO o)).Perm
    ((g.comps.filter (atO o)).map (Comp.map s.f))
  have hE : (g.pEnv.map (Comp.map s.f)).filter (atO o) = [] := by
    rw [filter_atO_map _ hf, List.filter_eq_nil_iff.2 (fun c hc => ?_), List.map_nil]
    have hc' : c ∈ g.comps ∧ c.label.isNone = true ∧ c.kind.isRandom = true := by
      unfold Graph.pEnv at hc
      simpa using hc
    simp [hO.random hc'.1 hc'.2.2]
  rw [List.filter_append, hE, List.append_nil, List.filter_map]
  have e1 : s.g.comps.filter (atO o ∘ rl (s.f x)) = s.g.comps.filter (atO o) :=
    List.filter_congr fun c _ => by rw [Function.comp_apply, rl_atO]
  rw [e1]
  have hO' : ∀ c ∈ s.g.comps.filter (atO o), c.kind.isRandom = false := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 (hs.subset hc)
    obtain ⟨hdc, hdo⟩ := List.mem_filter.1 hd
    rw [core_filter hO hlr] at hd
    have := hO.diff (List.mem_filter.1 hd).1 hdo
    simp only [Comp.map]
    cases hk : d.kind <;> simp_all [Kind.isRandom, Kind.isDiffusive]
  have e2 : (s.g.comps.filter (atO o)).map (rl (s.f x)) = s.g.comps.filter (atO o) := by
    conv_rhs => rw [← List.map_id (s.g.comps.filter (atO o))]
    refine List.map_congr_left fun c hc => ?_
    unfold rl
    simp [hO' c hc]
  rw [e2, ← core_filter hO hlr]
  exact hs

/-- The terms of `O^{(x),1}_weight` keep the components at `o`, if no regular weight is at `o`. -/
theorem w1_oout {o : Fin k} {x : Atom k n} {h : Graph k n}
    (hR : ∀ c ∈ h.comps, c.kind.isRandom = true → atO o c = false) :
    ∀ s ∈ oWeight1T x h, OOut o h s := by
  intro s hs
  unfold oWeight1T at hs
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
  obtain ⟨W₁, W₂, rest, h1, h2, h3, -⟩ := splitRegular_dec x h.comps p hp
  have hW : ∀ c ∈ W₁ ++ W₂, atO o c = false := by
    intro c hc
    obtain ⟨⟨ch, hk⟩, -, -⟩ := (isRegAt_iff x c).1 (h3 c hc)
    exact hR c (h1.symm.subset (List.mem_append_left _ hc)) (by rw [hk]; rfl)
  change (p.1.filter (atO o)).Perm ((h.comps.filter (atO o)).map (Comp.map id))
  rw [map_comp_id]
  refine (h2.filter _).trans ?_
  refine List.Perm.trans ?_ (h1.filter _).symm
  rw [List.filter_append, List.filter_append, List.filter_append]
  have e1 : (W₁.map toLight).filter (atO o) = [] := List.filter_eq_nil_iff.2 fun c hc => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    have : atO o (toLight d) = false := hW d (List.mem_append_left _ hd)
    simp [this]
  have e2 : W₁.filter (atO o) = [] :=
    List.filter_eq_nil_iff.2 fun c hc => by simp [hW c (List.mem_append_left _ hc)]
  have e3 : W₂.filter (atO o) = [] :=
    List.filter_eq_nil_iff.2 fun c hc => by simp [hW c (List.mem_append_right _ hc)]
  rw [e1, e2, e3]
  simp

/-- The terms of [II, (4.23)] keep the components at `o`, if no random component is at `o`. -/
theorem p2_oout {o : Fin k} {x : Atom k n} {h : Graph k n} (hx : x.isRight = true)
    (hR : ∀ c ∈ h.comps, c.kind.isRandom = true → atO o c = false)
    {E : TExpansion k n} (hE : oWeightP2Pos x h = some E) : ∀ s ∈ E, OOut o h s := by
  intro s hs
  obtain ⟨i, hi, hk, hxi, cs, co, rfl, hcs⟩ := mem_oWeightP2Pos hE hs
  have hxo : liftA 1 x ≠ (.inl o : Atom k (n + 1)) := by
    rw [Ne, liftA_iff]
    rintro rfl
    cases hx
  have hno : newA 0 ≠ (.inl o : Atom k (n + 1)) := by simp [newA]
  have hci : atO o h.comps[i] = false := hR _ (List.getElem_mem hi) (by rw [hk]; rfl)
  have hperm : (h.comps.filter (atO o)).Perm ((h.comps.eraseIdx i).filter (atO o)) := by
    have := (List.getElem_cons_eraseIdx_perm hi).filter (atO o)
    rw [List.filter_cons_of_neg (by simp [hci])] at this
    exact this.symm
  have hsx : atO o (mkC (.waved .s) (liftA 1 x) (newA 0)) = false := by simp [atO, mkC, hxo, hno]
  change (cs.filter (atO o)).Perm ((h.comps.filter (atO o)).map (Comp.map (liftA 1)))
  rcases hcs with rfl | rfl | ⟨j, hj, ps, hps, rfl⟩
  · rw [List.filter_append, liftCs, filter_atO_map _ (liftA_iff o)]
    have : ([mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light .plus) (newA 0) (newA 0)] :
        List (Comp (Atom k (n + 1)))).filter (atO o) = [] := by simp [atO, mkC, hxo, hno]
    rw [this, List.append_nil]
    exact List.Perm.map _ hperm.symm
  · rw [List.filter_append, liftCs, filter_atO_map _ (liftA_iff o)]
    have : ([mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.light .plus) (newA 0) (newA 0)] :
        List (Comp (Atom k (n + 1)))).filter (atO o) = [] := by simp [atO, mkC, hxo, hno]
    rw [this, List.append_nil]
  · have hc₀ : (h.comps.eraseIdx i)[j] ∈ h.comps :=
      List.mem_of_mem_eraseIdx (List.getElem_mem hj)
    have hr₀ : ((h.comps.eraseIdx i)[j]).kind.isRandom = true := by
      have := dPieces_random hps
      simpa [Comp.map] using this
    have hc₀o : atO o (h.comps.eraseIdx i)[j] = false := hR _ hc₀ hr₀
    have hc₀o' : atO o (((h.comps.eraseIdx i)[j]).map (liftA 1)) = false :=
      (atO_map (liftA_iff o) _).trans hc₀o
    have hps' := dPieces_atO hps hno hxo hc₀o'
    have hperm2 : ((h.comps.eraseIdx i).filter (atO o)).Perm
        (((h.comps.eraseIdx i).eraseIdx j).filter (atO o)) := by
      have := (List.getElem_cons_eraseIdx_perm hj).filter (atO o)
      rw [List.filter_cons_of_neg (by simp [hc₀o])] at this
      exact this.symm
    rw [List.filter_append, List.filter_append, liftCs, filter_atO_map _ (liftA_iff o)]
    have e1 : ps.filter (atO o) = [] :=
      List.filter_eq_nil_iff.2 fun c hc => by simp [hps' c hc]
    have e2 : ([mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 x)] :
        List (Comp (Atom k (n + 1)))).filter (atO o) = [] := by simp [atO, mkC, hxo, hno]
    rw [e1, e2, List.append_nil, List.append_nil]
    exact List.Perm.map _ (hperm.trans hperm2).symm

/-- The terms of [II, (4.24)] other than those with the label `Q_x` keep the components at `o`, if
no random component is at `o`. -/
theorem me_oout {o : Fin k} {x : Atom k n} {h : Graph k n} (hx : x.isRight = true)
    (hNL : ∀ c ∈ h.comps, c.kind.isSolid = true → c.x ≠ c.y)
    (hR : ∀ c ∈ h.comps, c.kind.isRandom = true → atO o c = false)
    {E : TExpansion k n} (hE : multiEHat x h = some E) :
    ∀ s ∈ E, (∃ c ∈ s.g.comps, c.label = some (.Q, s.f x)) ∨ OOut o h s := by
  intro s hs
  rcases shapes_multiEHat hNL hE s hs with hq | ⟨cs, co, rfl, hsh⟩
  · exact Or.inl hq
  right
  have hxo : liftA 1 x ≠ (.inl o : Atom k (n + 1)) := by
    rw [Ne, liftA_iff]
    rintro rfl
    cases hx
  have hno : newA 0 ≠ (.inl o : Atom k (n + 1)) := by simp [newA]
  have hxo' : x ≠ .inl o := by
    rintro rfl
    cases hx
  -- an edge at `x` of `h` has its other end away from `o`
  have hedge : ∀ r u, r ∈ h.comps → EdgeH x u r → u ≠ .inl o := by
    intro r u hr he hu
    have := hR r hr (Kind.isRandom_of_isSolid he.1)
    rcases he.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [atO, h2, hu] at this
    · simp [atO, h1, hu] at this
  have hnew : ∀ (u : Atom k n) (κ : Kind) (a : Comp (Atom k (n + 1))), u ≠ .inl o →
      NewH u κ a → atO o a = false := by
    intro u κ a hu ha
    have hu' : liftA 1 u ≠ (.inl o : Atom k (n + 1)) := by rw [Ne, liftA_iff]; exact hu
    rcases ha with rfl | rfl <;> simp [atO, mkC, hno, hu']
  have hsx : atO o (mkC (.waved .s) (liftA 1 x) (newA 0)) = false := by simp [atO, mkC, hxo, hno]
  -- the general form
  have key : ∀ (R B : List (Comp (Atom k n))) (A : List (Comp (Atom k (n + 1)))),
      h.comps.Perm (R ++ B) → (∀ r ∈ R, atO o r = false) → (∀ a ∈ A, atO o a = false) →
      ((liftCs 1 B ++ A).filter (atO o)).Perm
        ((h.comps.filter (atO o)).map (Comp.map (liftA 1))) := by
    intro R B A hRB hRo hAo
    have hA0 : A.filter (atO o) = [] := List.filter_eq_nil_iff.2 (fun a ha => by simp [hAo a ha])
    rw [List.filter_append, liftCs, filter_atO_map _ (liftA_iff o), hA0, List.append_nil]
    refine List.Perm.map _ ?_
    have := hRB.filter (atO o)
    have hR0 : R.filter (atO o) = [] := List.filter_eq_nil_iff.2 (fun r hr => by simp [hRo r hr])
    rw [List.filter_append, hR0, List.nil_append] at this
    exact this.symm
  change (cs.filter (atO o)).Perm ((h.comps.filter (atO o)).map (Comp.map (liftA 1)))
  rcases hsh with ⟨r₁, r₂, B, u₁, u₂, a₁, a₂, X, hP, he₁, he₂, hn₁, hn₂, hX, -, rfl⟩ |
    ⟨r₁, B, u₁, a₁, b, ch, hP, he₁, hn₁, hb, hcs⟩ | ⟨ch, rfl⟩ |
    ⟨r, c, B, z, p, q, ps, e₀, hP, he, hcr, -, hpq, hps, hn, rfl⟩
  · have hr₁ := hP.symm.subset (by simp : r₁ ∈ [r₁, r₂] ++ B)
    have hr₂ := hP.symm.subset (by simp : r₂ ∈ [r₁, r₂] ++ B)
    refine key [r₁, r₂] B _ hP ?_ ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hR _ hr₁ (Kind.isRandom_of_isSolid he₁.1)
      · exact hR _ hr₂ (Kind.isRandom_of_isSolid he₂.1)
    · intro a ha
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with (rfl | rfl | rfl) | ha
      · exact hsx
      · exact hnew _ _ _ (hedge _ _ hr₁ he₁) hn₁
      · exact hnew _ _ _ (hedge _ _ hr₂ he₂) hn₂
      · obtain ⟨ch, rfl⟩ := hX a ha
        simp [atO, mkC, hxo]
  · have hr₁ := hP.symm.subset (by simp : r₁ ∈ [r₁] ++ B)
    have hbo : atO o b = false := hnew _ _ _ hxo' hb
    have ha₁ : atO o a₁ = false := hnew _ _ _ (hedge _ _ hr₁ he₁) hn₁
    have hRo : ∀ r ∈ [r₁], atO o r = false := by
      intro r hr
      rw [List.mem_singleton.1 hr]
      exact hR _ hr₁ (Kind.isRandom_of_isSolid he₁.1)
    rcases hcs with rfl | rfl
    · refine key [r₁] B _ hP hRo ?_
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact hsx
      · exact ha₁
      · exact hbo
    · refine key [r₁] B _ hP hRo ?_
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact hsx
      · exact hbo
      · exact ha₁
  · refine key [] h.comps _ (by simp) (by simp) ?_
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hsx
    · simp [atO, mkC, hno]
  · have hr := hP.symm.subset (by simp : r ∈ [r, c] ++ B)
    have hc := hP.symm.subset (by simp : c ∈ [r, c] ++ B)
    have hco : atO o c = false := hR _ hc hcr
    have hco' : atO o (c.map (liftA 1)) = false := (atO_map (liftA_iff o) _).trans hco
    have hpo : p ≠ .inl o := by rcases hpq with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hqo : q ≠ .inl o := by rcases hpq with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
    have hps' := dPieces_atO hps hpo hqo hco'
    refine key [r, c] B _ hP ?_ ?_
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact hR _ hr (Kind.isRandom_of_isSolid he.1)
      · exact hco
    · intro a ha
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with ha | rfl | rfl
      · exact hps' a ha
      · exact hsx
      · exact hnew _ _ _ (hedge _ _ hr he) hn

theorem filter_conjC {m : ℕ} {o : Fin k} (L : List (Comp (Atom k m))) :
    (L.map conjC).filter (atO o) = (L.filter (atO o)).map conjC := by
  rw [List.filter_map]
  rfl

/-- The terms of the complex conjugate of an identity applied to `h.conj`. -/
theorem conj_oout {o : Fin k} {h : Graph k n} {E : TExpansion k n}
    (hE : ∀ s ∈ E, OOut o h.conj s) : ∀ s ∈ E.conj, OOut o h s := by
  intro s hs
  obtain ⟨s₀, hs₀, rfl⟩ := mem_TExpansion_conj.1 hs
  have h0 := hE s₀ hs₀
  change ((s₀.g.conj.comps).filter (atO o)).Perm ((h.comps.filter (atO o)).map (Comp.map s₀.f))
  change (s₀.g.comps.filter (atO o)).Perm ((h.conj.comps.filter (atO o)).map (Comp.map s₀.f)) at h0
  rw [Graph.conj_comps'] at h0 ⊢
  rw [filter_conjC] at h0 ⊢
  refine (List.Perm.map conjC h0).trans (List.Perm.of_eq ?_)
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun c _ => ?_
  simp only [Function.comp_apply]
  rw [conjC_map, conjC_conjC]

/-- The random components of `h.conj` are not at `o` if those of `h` are not. -/
theorem conj_random {o : Fin k} {h : Graph k n}
    (hR : ∀ c ∈ h.comps, c.kind.isRandom = true → atO o c = false) :
    ∀ c ∈ h.conj.comps, c.kind.isRandom = true → atO o c = false := by
  intro c hc hr
  rw [Graph.conj_comps'] at hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  refine hR d hd ?_
  have hk : ∀ κ : Kind, κ.conj.isRandom = κ.isRandom := by
    intro κ
    cases κ with
    | waved w => cases w <;> rfl
    | _ => rfl
  rw [← hk]
  exact hr

/-- The terms of one step inside `P_x` (`O^{(x),1}_weight`, [II, (4.23)], [II, (4.24)]) keep the
components at the external atoms. -/
theorem opTerms_oo1 {C : ℕ} {x : Atom k n} {g : Graph k n} (hS : St C x g) :
    (∀ t ∈ pLiftT x g (oWeight1T x g.pCore), OO1 g t) ∧ (∀ t ∈ oWeightP2T x g, OO1 g t) ∧
    (∀ E, multiEHat x g.pCore = some E → ∀ t ∈ pLiftT x g E, OO1 g t) := by
  have hN := hS.nn
  have hlr := hN.plain.labRand
  have hid : ∀ o (u : Atom k n), (id u : Atom k n) = .inl o ↔ u = .inl o := fun _ _ => Iff.rfl
  refine ⟨?_, ?_, ?_⟩
  · intro t ht o hO
    obtain ⟨s, hs, -, rfl⟩ := mem_pLiftT.1 ht
    have hso := w1_oout (fun c hc hr => core_random hO hc hr) s hs
    have hs' := hs
    unfold oWeight1T at hs'
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hs'
    exact pLift_oout hO hlr (fun u => hid o u) hso
  · intro t ht o hO
    have hR : ∀ c ∈ g.pCore.comps, c.kind.isRandom = true → atO o c = false :=
      fun c hc hr => core_random hO hc hr
    unfold oWeightP2T at ht
    rcases hE : oWeightP2Pos x g.pCore with _ | E
    · rw [hE] at ht
      dsimp only at ht
      rcases hE' : oWeightP2Pos x g.pCore.conj with _ | E
      · rw [hE'] at ht
        dsimp only at ht
        rw [List.mem_singleton.1 ht]
        exact OOut.self o g
      · rw [hE'] at ht
        dsimp only at ht
        obtain ⟨s, hs, -, rfl⟩ := mem_pLiftT.1 ht
        have hso := conj_oout (p2_oout hN.hx (conj_random hR) hE') s hs
        obtain ⟨s₀, hs₀, rfl⟩ := mem_TExpansion_conj.1 hs
        obtain ⟨_, _, _, _, _, _, rfl, _⟩ := mem_oWeightP2Pos hE' hs₀
        exact pLift_oout hO hlr (fun u => liftA_iff o u) hso
    · rw [hE] at ht
      dsimp only at ht
      obtain ⟨s, hs, -, rfl⟩ := mem_pLiftT.1 ht
      have hso := p2_oout hN.hx hR hE s hs
      obtain ⟨_, _, _, _, _, _, rfl, _⟩ := mem_oWeightP2Pos hE hs
      exact pLift_oout hO hlr (fun u => liftA_iff o u) hso
  · intro E hE t ht o hO
    have hR : ∀ c ∈ g.pCore.comps, c.kind.isRandom = true → atO o c = false :=
      fun c hc hr => core_random hO hc hr
    obtain ⟨s, hs, hq, rfl⟩ := mem_pLiftT.1 ht
    rcases me_oout hN.hx (noLoop_core hS) hR hE s hs with ⟨c, hc, hl⟩ | hso
    · exfalso
      have := List.any_eq_false.1 hq c hc
      simp [hl] at this
    · rcases shapes_multiEHat (noLoop_core hS) hE s hs with ⟨c, hc, hl⟩ | ⟨cs, co, rfl, -⟩
      · exfalso
        have := List.any_eq_false.1 hq c hc
        simp [hl] at this
      · exact pLift_oout hO hlr (fun u => liftA_iff o u) hso

end OTerms


section OSteps

variable {k : ℕ}

/-- Replacing a component that is not diffusive by a component at an external atom only if the
replaced one is keeps the components at the external atoms. -/
theorem PStepsOK1.set {n : ℕ} {Γ T : Graph k n} (h : PStepsOK1 Γ T) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hcd : c.kind.isDiffusive = false) (c' : Comp (Atom k n))
    (hc' : ∀ o : Fin k, atO o c' = true → atO o c = true) (co : Coeff) :
    PStepsOK1 Γ ⟨T.comps.set i c', co⟩ := by
  intro o hO
  have hi : i < T.comps.length := (List.getElem?_eq_some_iff.1 hc).1
  have hp₁ : (T.comps.set i c').Perm (c' :: T.comps.eraseIdx i) := by
    have h1 : (T.comps.set i c')[i]? = some c' := by simp [hi]
    have := perm_cons_eraseIdx h1
    rwa [List.eraseIdx_set_eq] at this
  have hco : atO o c = false := (h o hO).atO_false hO (List.mem_of_getElem? hc) hcd
  have hco' : atO o c' = false := by
    cases e : atO o c'
    · rfl
    · rw [hc' o e] at hco
      cases hco
  change ((T.comps.set i c').filter (atO o)).Perm _
  refine (hp₁.filter _).trans ?_
  rw [List.filter_cons_of_neg (by simp [hco'])]
  exact (h o hO).erase hc hco T.coeff

/-- A component that is not diffusive of a graph with only diffusive components at `o` has no end
at `o`. -/
theorem ends_off {n : ℕ} {o : Fin k} {g : Graph k n} (hO : ODiff o g)
    {c : Comp (Atom k n)} (hc : c ∈ g.comps) (hd : c.kind.isDiffusive = false) :
    c.x ≠ .inl o ∧ c.y ≠ .inl o := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hO c hc (Or.inl h)] at hd
    cases hd
  · rw [hO c hc (Or.inr h)] at hd
    cases hd

theorem OOut.of_keep {n : ℕ} {o : Fin k} {g g₁ : Graph k n} {s : Tracked k n}
    (h : OOut o g₁ s) (hk : OKeep o g g₁) : OOut o g s :=
  h.trans (List.Perm.map _ hk)

end OSteps


section ORebase

variable {k n : ℕ}

end ORebase

section ORebaseAll

variable {k n : ℕ}

end ORebaseAll

section OIdentify

variable {k n : ℕ}

end OIdentify

section ONormalize

variable {k : ℕ}

end ONormalize

section OInit

variable {k n : ℕ}

end OInit

section ORound

variable {k : ℕ}

end ORound

end RBM8D.Graphs
