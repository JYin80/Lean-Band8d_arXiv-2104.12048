module

public import RBM8D.LocalLaw.LabelRemoval
public import RBM8D.Bound.GraphSum
public import RBM8D.Bound.KeySum
public import RBM8D.Input.LDELin
public import RBM8D.Graph.Local.Model

@[expose] public section

/-!
# The `Q`-graphs in the high moment ([II, Claim 8.7])

Facts on the graphs of `Q_T^{(n)}` used in the proof of [II, Claim 8.7]. Every such graph is a
`Q`-graph with one label `Q_u`; its value is `Σ_σ c_σ Q_{σ(u)} R_σ` with deterministic `c_σ` and a
product `R_σ` of resolvent entries.

* The exchange of `Q_x`: `E(F · Q_x G) = E(Q_x F · G)` and `E Q_x F = 0` (`QTerm_swap`, `QTerm_E_Q`).
* The labels of a `Q`-graph (`QTerm_labels_eq`), the value of a `Q`-graph (`QTerm_termR_eq`,
  `QTerm_det_const`, `QTerm_abs_term`), and the value at `G = m` of a graph without random
  component (`QTerm_Gm_empty`).
* Polynomial growth and measurability of the value of a graph (`QTerm_polyMeas_valR`), and the large
  deviation bound for a polynomial of Gaussian entries (`QTerm_lde_prob`).
* Graphs with an internal atom that are not `⊕`-recollision graphs at `𝔟₁ = 𝔟₂`: the label atom is
  internal, by [II, Def 6.3 (3)] and the clause on the external atoms (`QTerm_label_internal`).
* The description of the dotted blocks of a graph by the connected components of its dotted edges.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal

namespace RBM8D

open Graphs

/-! ## The partial expectations -/

section Swap

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `E (F · Q_x G) = E (Q_x F · G)` for functions of polynomial growth. -/
lemma QTerm_swap (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hS0 : ∀ x y, 0 ≤ S x y) (x : ι)
    (F G : Sample ι → ℂ) (hF : PolyMeas F) (hG : PolyMeas G) :
    ∫ ω, F ω * (G ω - Pexp S x G ω) ∂(gaussLaw S) =
      ∫ ω, (F ω - Pexp S x F ω) * G ω ∂(gaussLaw S) := by
  have hL := pqLaws_Pexp_poly S hS hS0
  have hPF := hL.adm_P x F hF
  have hPG := hL.adm_P x G hG
  have i1 := integrable_of_polyMeas S _ (hL.adm_mul _ _ hF hG)
  have i2 := integrable_of_polyMeas S _ (hL.adm_mul _ _ hF hPG)
  have i3 := integrable_of_polyMeas S _ (hL.adm_mul _ _ hPF hG)
  have e1 : ∫ ω, F ω * Pexp S x G ω ∂(gaussLaw S) =
      ∫ ω, Pexp S x G ω * Pexp S x F ω ∂(gaussLaw S) := by
    have e := hL.E_P x (Pexp S x G * F) (hL.adm_mul _ _ hPG hF)
    rw [hL.P_mul_free x F (Pexp S x G) (hL.free_P x G)] at e
    simp only [Pi.mul_apply] at e
    rw [e]
    exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
  have e2 : ∫ ω, Pexp S x F ω * G ω ∂(gaussLaw S) =
      ∫ ω, Pexp S x F ω * Pexp S x G ω ∂(gaussLaw S) := by
    have e := hL.E_P x (Pexp S x F * G) (hL.adm_mul _ _ hPF hG)
    rw [hL.P_mul_free x G (Pexp S x F) (hL.free_P x F)] at e
    simp only [Pi.mul_apply] at e
    exact e.symm
  have e3 : ∫ ω, Pexp S x G ω * Pexp S x F ω ∂(gaussLaw S) =
      ∫ ω, Pexp S x F ω * Pexp S x G ω ∂(gaussLaw S) :=
    integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
  simp_rw [mul_sub, sub_mul]
  rw [integral_sub (by exact i1) (by exact i2), integral_sub (by exact i1) (by exact i3), e1, e3,
    e2]

/-- `E Q_x F = 0` for a function of polynomial growth. -/
lemma QTerm_E_Q (S : Matrix ι ι ℝ) (hS : S.IsSymm) (hS0 : ∀ x y, 0 ≤ S x y) (x : ι)
    (F : Sample ι → ℂ) (hF : PolyMeas F) :
    ∫ ω, (F ω - Pexp S x F ω) ∂(gaussLaw S) = 0 := by
  have hL := pqLaws_Pexp_poly S hS hS0
  have i1 := integrable_of_polyMeas S _ hF
  have i2 := integrable_of_polyMeas S _ (hL.adm_P x F hF)
  rw [integral_sub i1 i2]
  have e := hL.E_P x F hF
  change ∫ ω, Pexp S x F ω ∂(gaussLaw S) = ∫ ω, F ω ∂(gaussLaw S) at e
  rw [e, sub_self]

end Swap

/-! ## The value of a `Q`-graph -/

section QValue

/-- The labels of a graph whose labelled components all carry the label `(Q, u)`, one of them at
least: the single label `(Q, u)`. -/
lemma QTerm_labels_eq {k n : ℕ} (g : Graph k n) (u : Atom k n)
    (hu : ∃ c ∈ g.comps, c.label = some (.Q, u))
    (hall : ∀ c ∈ g.comps, (c.kind.isRandom = true ∨ c.label.isSome = true) →
      c.label = some (.Q, u)) :
    g.labels = [(.Q, u)] := by
  unfold Graph.labels
  set l := g.comps.filterMap Comp.label with hl
  have hall' : ∀ ℓ ∈ l, ℓ = (.Q, u) := by
    intro ℓ hℓ
    obtain ⟨c, hc, hcl⟩ := List.mem_filterMap.1 hℓ
    have := hall c hc (Or.inr (by rw [hcl]; rfl))
    rw [this] at hcl
    exact (Option.some.inj hcl).symm
  have hmem : (PQ.Q, u) ∈ l := by
    obtain ⟨c, hc, hcl⟩ := hu
    exact List.mem_filterMap.2 ⟨c, hc, hcl⟩
  have hsub : ∀ ℓ ∈ l.dedup, ℓ = (.Q, u) := fun ℓ hℓ => hall' ℓ (List.mem_dedup.1 hℓ)
  have hnd := List.nodup_dedup l
  have hne : (PQ.Q, u) ∈ l.dedup := List.mem_dedup.2 hmem
  rcases hd : l.dedup with _ | ⟨a, t⟩
  · rw [hd] at hne; simp at hne
  · rw [hd] at hsub hnd
    have ha := hsub a (List.mem_cons_self ..)
    cases t with
    | nil => rw [ha]
    | cons b t =>
      have hb := hsub b (by simp)
      exfalso
      apply (List.nodup_cons.1 hnd).1
      rw [ha, ← hb]
      simp

/-- The product of the factors of the components with the label `(Q, u)` at the labelling `σ`, as a
function of the sample. -/
def QTerm_lab {k n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (g : Graph k n)
    (u : Atom k n) (D : Sample ι → Data ι) (σ : Atom k n → ι) : Sample ι → ℂ :=
  fun ω => ((g.comps.filter fun c => decide (c.label = some (.Q, u))).map (Comp.val (D ω) σ)).prod

/-- The coefficient times the factors of the unlabelled components at the labelling `σ`. -/
def QTerm_det {k n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (g : Graph k n)
    (D : Data ι) (σ : Atom k n → ι) : ℂ :=
  g.coeff.eval D.m * ((g.comps.filter fun c => c.label.isNone).map (Comp.val D σ)).prod

/-- The term of a graph with the single label `(Q, u)` at the labelling `σ`:
`c_σ (R_σ − P_{σ u} R_σ)`. -/
lemma QTerm_termR_eq {k n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (g : Graph k n)
    (u : Atom k n) (hl : g.labels = [(.Q, u)]) (S : Matrix ι ι ℝ) (D : Sample ι → Data ι)
    (σ : Atom k n → ι) (ω : Sample ι) :
    g.termR ⟨Pexp S⟩ D σ ω =
      QTerm_det g (D ω) σ * (QTerm_lab g u D σ ω - Pexp S (σ u) (QTerm_lab g u D σ) ω) := by
  unfold Graph.termR QTerm_det
  rw [hl]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, PFamily.op,
    Pi.sub_apply]
  rfl

/-- Components that are not random read no resolvent entry: their factor on the data record of
the model does not depend on the sample. -/
private lemma QTerm_val_det {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ) [NeZero L]
    (z : ℂ) (ω ω' : Sample (Zd d L)) {V : Type*} (σ : V → Zd d L) (c : Comp V)
    (hc : c.kind.isRandom = false) :
    Comp.val (rbmData d P Sig W L z ω) σ c = Comp.val (rbmData d P Sig W L z ω') σ c := by
  rcases c with ⟨κ, x, y, mi, lab⟩
  cases κ with
  | G ch => simp [Kind.isRandom] at hc
  | weight ch => simp [Kind.isRandom] at hc
  | light ch => simp [Kind.isRandom] at hc
  | inv ch => simp [Kind.isRandom] at hc
  | wD ch D => simp [Kind.isRandom] at hc
  | waved w => cases w <;> rfl
  | theta o => rfl
  | thetaErr n D => rfl
  | ghost => rfl
  | aux j r b => rfl
  | dot => rfl
  | xdot => rfl

/-- On a graph whose random components all carry a label, `c_σ` does not depend on the sample. -/
lemma QTerm_det_const {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ)
    [NeZero L] (z : ℂ) {k n : ℕ} (g : Graph k n)
    (hR : ∀ c ∈ g.comps, c.kind.isRandom = true → c.label.isSome = true)
    (σ : Atom k n → Zd d L) (ω ω' : Sample (Zd d L)) :
    QTerm_det g (rbmData d P Sig W L z ω) σ = QTerm_det g (rbmData d P Sig W L z ω') σ := by
  unfold QTerm_det
  have hm : (rbmData d P Sig W L z ω).m = (rbmData d P Sig W L z ω').m := rfl
  rw [hm]
  congr 1
  refine congrArg List.prod (List.map_congr_left fun c hc => ?_)
  obtain ⟨hc, hn⟩ := List.mem_filter.1 hc
  refine QTerm_val_det P Sig W L z ω ω' σ c ?_
  by_contra h
  have := hR c hc (by simpa using h)
  simp_all

/-- `cmat (Ring.inverse B) = Ring.inverse (cmat B)`. -/
private lemma QTerm_cmat_ringInverse {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ) :
    cmat (Ring.inverse B) = Ring.inverse (cmat B) := by
  let f : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix
  change f (Ring.inverse B) = Ring.inverse (f B)
  by_cases h : IsUnit B
  · obtain ⟨u, rfl⟩ := h
    have : f (u : Matrix ι ι ℝ) = ((Units.map f.toMonoidHom u : (Matrix ι ι ℂ)ˣ) : Matrix ι ι ℂ) :=
      rfl
    rw [this, Ring.inverse_unit, Ring.inverse_unit]
    rfl
  · have h' : ¬ IsUnit (f B) := by
      intro h2
      apply h
      rw [Matrix.isUnit_iff_isUnit_det] at h2 ⊢
      rw [isUnit_iff_ne_zero] at h2 ⊢
      intro h0
      apply h2
      have := RingHom.map_det Complex.ofRealHom B
      change Complex.ofRealHom B.det = (f B).det at this
      rw [← this, h0, map_zero]
    rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h']
    ext i j
    simp

/-- `cmat Θ = |m|² S (1 − |m|² S)⁻¹` over `ℂ`. -/
private lemma QTerm_cmat_Theta {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (m : ℂ) :
    cmat (Theta m S) =
      (((‖m‖ : ℂ) ^ 2) • cmat S) * Ring.inverse (1 - ((‖m‖ : ℂ) ^ 2) • cmat S) := by
  have h1 : ∀ T : Matrix ι ι ℝ, cmat (‖m‖ ^ 2 • T) = ((‖m‖ : ℂ) ^ 2) • cmat T := fun T => by
    ext i j
    simp [cmat]
  have h2 : cmat (1 - ‖m‖ ^ 2 • S) = 1 - ((‖m‖ : ℂ) ^ 2) • cmat S := by
    ext i j
    simp only [cmat, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply]
    split_ifs <;> simp
  have h3 : ∀ A B : Matrix ι ι ℝ, cmat (A * B) = cmat A * cmat B := fun A B =>
    Matrix.map_mul (f := Complex.ofRealHom)
  rw [Theta, h3, QTerm_cmat_ringInverse, h1, h2]

/-- Every component with the kinds of [II, Def 3.2] has the same factor on the data record of the
model at `ω` and on the data record at the single matrix `G(ω)`. -/
private lemma QTerm_val_rbm {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ)
    [NeZero L] (z : ℂ) (ω : Sample (Zd d L)) {V : Type*} (σ : V → Zd d L) (N : ℕ) (c : Comp V)
    (hc : c.isTKind N = true) :
    Comp.val (rbmData d P Sig W L z ω) σ c =
      Comp.val (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)) σ c := by
  have hmin : c.minor = [] := by
    have := hc; simp only [Comp.isTKind, Bool.and_eq_true, List.isEmpty_iff] at this
    exact this.1
  have hGm : (rbmData d P Sig W L z ω).Gm ((c.minor.map σ).toFinset) = green (hmat ω) z := by
    rw [hmin]
    simp only [rbmData, modelData, List.map_nil, List.toFinset_nil]
    rw [dite_eq_right]
    rintro ⟨x, hx⟩
    exact (Finset.singleton_ne_empty x) hx.symm
  have hSp : (rbmData d P Sig W L z ω).Sp = (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)).Sp := by
    simp only [rbmData, modelData, gData, detData, Splus, cmat, Matrix.nonsing_inv_eq_ringInverse]
  have hTh : (rbmData d P Sig W L z ω).Theta =
      (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)).Theta := by
    simp only [rbmData, modelData, gData, detData]
    rw [QTerm_cmat_Theta, Matrix.nonsing_inv_eq_ringInverse]
    push_cast
    rfl
  have hSig : (rbmData d P Sig W L z ω).Sig = (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)).Sig :=
    rfl
  have hchain : ∀ o, (rbmData d P Sig W L z ω).chain o =
      (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)).chain o := by
    intro o; unfold Data.chain; rw [hTh, hSig]
  obtain ⟨κ, x, y, mi, l⟩ := c
  cases κ with
  | G ch => simp only [Comp.val] at hGm ⊢; rw [hGm]; rfl
  | weight ch => simp only [Comp.val] at hGm ⊢; rw [hGm]; rfl
  | light ch => simp only [Comp.val] at hGm ⊢; rw [hGm]; rfl
  | waved w =>
    cases w with
    | s => rfl
    | plus => simp only [Comp.val]; rw [hSp]
    | minus =>
      have hSm : (rbmData d P Sig W L z ω).Sm =
          (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)).Sm := by
        simp only [rbmData, modelData, gData, detData, Sminus, Splus, cmat,
          Matrix.nonsing_inv_eq_ringInverse]
        rfl
      simp only [Comp.val]; rw [hSm]
  | theta o => simp only [Comp.val]; rw [hchain]
  | dot => rfl
  | xdot => rfl
  | _ => simp [Comp.isTKind] at hc

/-- For a graph with the kinds of [II, Def 3.2] whose labels are all `(Q, u)`, the summand of the
absolute-value graph at the single matrix `G(ω)` is `|c_σ| |R_σ(ω)|`. -/
lemma QTerm_abs_term {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ)
    [NeZero L] (z : ℂ) {n N : ℕ} (g : Graph 3 n) (hK : g.TKinds N) (u : Atom 3 n)
    (hlab : ∀ c ∈ g.comps, c.label = none ∨ c.label = some (.Q, u))
    (σ : Atom 3 n → Zd d L) (ω : Sample (Zd d L)) :
    ‖g.coeff.eval (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)).m‖ *
        (g.comps.map fun c => ‖Comp.val (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)) σ c‖).prod
      = ‖QTerm_det g (rbmData d P Sig W L z ω) σ‖ *
        ‖QTerm_lab g u (rbmData d P Sig W L z) σ ω‖ := by
  have hTK : ∀ c ∈ g.comps, c.isTKind N = true := fun c hc => List.all_eq_true.1 hK c hc
  have hv : ∀ c ∈ g.comps, ‖Comp.val (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)) σ c‖ =
      ‖Comp.val (rbmData d P Sig W L z ω) σ c‖ := fun c hc => by
    rw [QTerm_val_rbm P Sig W L z ω σ N c (hTK c hc)]
  rw [List.map_congr_left hv]
  unfold QTerm_det QTerm_lab
  rw [norm_mul, List.norm_prod, List.norm_prod, List.map_map, List.map_map, mul_assoc]
  have hm : (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)).m = (rbmData d P Sig W L z ω).m := rfl
  rw [hm]
  congr 1
  have hsplit := List.prod_map_filter_mul_prod_map_filter_not (fun c : Comp (Atom 3 n) =>
    c.label.isNone = true) (fun c => ‖Comp.val (rbmData d P Sig W L z ω) σ c‖) g.comps
  have hf : (g.comps.filter fun c => decide ¬ (c.label.isNone = true)) =
      g.comps.filter fun c => decide (c.label = some (.Q, u)) :=
    List.filter_congr fun c hc => by rcases hlab c hc with h | h <;> simp [h]
  rw [← hsplit, hf]
  rfl

end QValue

section Box

variable {d L : ℕ} [NeZero L]

end Box


section HookMat

variable {d L : ℕ} [NeZero L]

end HookMat


section Good

variable {d L : ℕ} [NeZero L]

end Good


section HookBound

variable {d L : ℕ} [NeZero L]

end HookBound

/-! ## The filter of the local law -/

/-- The resolvent of the data record of the model. -/
lemma QTerm_Gm_empty (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ)
    [NeZero L] (z : ℂ) (ω : Sample (Zd d L)) :
    (rbmData d P Sig W L z ω).Gm ∅ = green (hmat ω) z := by
  have h : ¬ ∃ x : Zd d L, (∅ : Finset (Zd d L)) = {x} := by
    rintro ⟨x, hx⟩
    exact Finset.singleton_ne_empty x hx.symm
  simp only [rbmData, modelData, dite_eq_right h]

/-! ## A priori bounds and measurability of graph values -/

/-- The products of the factors of components with the kinds of [II, Def 3.2] on the data record
of the model have polynomial growth. -/
private lemma QTerm_polyMeas_prod (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ)
    [NeZero L] (z : ℂ) (hz : 0 < z.im) (hS : (Smat P.ψ W L).IsSymm)
    (hnn : ∀ x y, 0 ≤ Smat P.ψ W L x y) {k n N : ℕ} (Γ : Graph k n) (hΓ : Γ.TKinds N)
    (σ : Atom k n → Zd d L) (l : List (Comp (Atom k n))) (hl : ∀ c ∈ l, c ∈ Γ.comps) :
    PolyMeas fun ω => (l.map (Comp.val (rbmData d P Sig W L z ω) σ)).prod := by
  have hL := pqLaws_Pexp_poly (Smat P.ψ W L) hS hnn
  have hGm := QTerm_Gm_empty d P Sig W L z
  have hgreen : ∀ x y, PolyMeas fun ω : Sample (Zd d L) => green (hmat ω) z x y :=
    fun x y => polyMeas_of_testFn _ (testFn_green z hz.ne' x y)
  have hconst : ∀ (f : Sample (Zd d L) → ℂ) (a : ℂ), (∀ ω, f ω = a) → PolyMeas f := by
    intro f a h
    have : f = fun _ => a := funext h
    rw [this]; exact hL.adm_const a
  have hcomp : ∀ (σ : Atom k n → Zd d L), ∀ c ∈ Γ.comps,
      PolyMeas fun ω => Comp.val (rbmData d P Sig W L z ω) σ c := by
    intro σ c hc
    have hc' := List.all_eq_true.1 hΓ c hc
    rcases c with ⟨κ, x, y, mi, lab⟩
    have hmi : mi = [] := by
      simp only [Comp.isTKind, Bool.and_eq_true, List.isEmpty_iff] at hc'
      exact hc'.1
    subst hmi
    cases κ with
    | G ch =>
      cases ch
      · simpa [Comp.val, Charge.apply, hGm] using hgreen (σ x) (σ y)
      · simpa [Comp.val, Charge.apply, hGm] using hL.adm_conj _ (hgreen (σ x) (σ y))
    | weight ch =>
      cases ch
      · simpa [Comp.val, Charge.apply, hGm] using hgreen (σ x) (σ x)
      · simpa [Comp.val, Charge.apply, hGm] using hL.adm_conj _ (hgreen (σ x) (σ x))
    | light ch =>
      have h1 : PolyMeas fun ω : Sample (Zd d L) => green (hmat ω) z (σ x) (σ x) - msc z := by
        have := hL.adm_add _ _ (hgreen (σ x) (σ x)) (hL.adm_const (-msc z))
        refine (congrArg PolyMeas ?_).mp this
        funext ω
        simp [sub_eq_add_neg]
      cases ch
      · simpa [Comp.val, Charge.apply, hGm, rbmData, modelData] using h1
      · simpa [Comp.val, Charge.apply, hGm, rbmData, modelData] using hL.adm_conj _ h1
    | waved w => cases w <;> exact hconst _ _ fun ω => rfl
    | theta o => exact hconst _ ((rbmData d P Sig W L z 0).chain o (σ x) (σ y)) fun ω => rfl
    | dot => exact hconst _ _ fun ω => rfl
    | xdot => exact hconst _ _ fun ω => rfl
    | _ => simp [Comp.isTKind] at hc'
  have hprod : ∀ (σ : Atom k n → Zd d L) (l : List (Comp (Atom k n))), (∀ c ∈ l, c ∈ Γ.comps) →
      PolyMeas fun ω => (l.map (Comp.val (rbmData d P Sig W L z ω) σ)).prod := by
    intro σ l hl
    induction l with
    | nil => simpa using hL.adm_const 1
    | cons c l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact hL.adm_mul _ _ (hcomp σ c (hl c (List.mem_cons_self ..)))
        (ih fun c' hc' => hl c' (List.mem_cons_of_mem _ hc'))
  exact hprod σ l hl

/-- The values of the graphs with the kinds of [II, Def 3.2] on the data record of the model have
polynomial growth; in particular they are measurable. -/
lemma QTerm_polyMeas_valR (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ)
    [NeZero L] (z : ℂ) (hz : 0 < z.im) (hS : (Smat P.ψ W L).IsSymm)
    (hnn : ∀ x y, 0 ≤ Smat P.ψ W L x y) {k n N : ℕ} (Γ : Graph k n) (hΓ : Γ.TKinds N)
    (e : Fin k → Zd d L) :
    PolyMeas (Γ.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) e) := by
  have hL := pqLaws_Pexp_poly (Smat P.ψ W L) hS hnn
  have hGm := QTerm_Gm_empty d P Sig W L z
  have hgreen : ∀ x y, PolyMeas fun ω : Sample (Zd d L) => green (hmat ω) z x y :=
    fun x y => polyMeas_of_testFn _ (testFn_green z hz.ne' x y)
  have hconst : ∀ (f : Sample (Zd d L) → ℂ) (a : ℂ), (∀ ω, f ω = a) → PolyMeas f := by
    intro f a h
    have : f = fun _ => a := funext h
    rw [this]; exact hL.adm_const a
  have hcomp : ∀ (σ : Atom k n → Zd d L), ∀ c ∈ Γ.comps,
      PolyMeas fun ω => Comp.val (rbmData d P Sig W L z ω) σ c := by
    intro σ c hc
    have hc' := List.all_eq_true.1 hΓ c hc
    rcases c with ⟨κ, x, y, mi, lab⟩
    have hmi : mi = [] := by
      simp only [Comp.isTKind, Bool.and_eq_true, List.isEmpty_iff] at hc'
      exact hc'.1
    subst hmi
    cases κ with
    | G ch =>
      cases ch
      · simpa [Comp.val, Charge.apply, hGm] using hgreen (σ x) (σ y)
      · simpa [Comp.val, Charge.apply, hGm] using hL.adm_conj _ (hgreen (σ x) (σ y))
    | weight ch =>
      cases ch
      · simpa [Comp.val, Charge.apply, hGm] using hgreen (σ x) (σ x)
      · simpa [Comp.val, Charge.apply, hGm] using hL.adm_conj _ (hgreen (σ x) (σ x))
    | light ch =>
      have h1 : PolyMeas fun ω : Sample (Zd d L) => green (hmat ω) z (σ x) (σ x) - msc z := by
        have := hL.adm_add _ _ (hgreen (σ x) (σ x)) (hL.adm_const (-msc z))
        refine (congrArg PolyMeas ?_).mp this
        funext ω
        simp [sub_eq_add_neg]
      cases ch
      · simpa [Comp.val, Charge.apply, hGm, rbmData, modelData] using h1
      · simpa [Comp.val, Charge.apply, hGm, rbmData, modelData] using hL.adm_conj _ h1
    | waved w => cases w <;> exact hconst _ _ fun ω => rfl
    | theta o => exact hconst _ ((rbmData d P Sig W L z 0).chain o (σ x) (σ y)) fun ω => rfl
    | dot => exact hconst _ _ fun ω => rfl
    | xdot => exact hconst _ _ fun ω => rfl
    | _ => simp [Comp.isTKind] at hc'
  have hprod : ∀ (σ : Atom k n → Zd d L) (l : List (Comp (Atom k n))), (∀ c ∈ l, c ∈ Γ.comps) →
      PolyMeas fun ω => (l.map (Comp.val (rbmData d P Sig W L z ω) σ)).prod := by
    intro σ l hl
    induction l with
    | nil => simpa using hL.adm_const 1
    | cons c l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact hL.adm_mul _ _ (hcomp σ c (hl c (List.mem_cons_self ..)))
        (ih fun c' hc' => hl c' (List.mem_cons_of_mem _ hc'))
  have hterm : ∀ σ : Atom k n → Zd d L,
      PolyMeas fun ω => Γ.termR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) σ ω := by
    intro σ
    unfold Graph.termR
    refine hL.adm_mul _ _ (hL.adm_mul _ _ (hconst _ (Γ.coeff.eval (msc z)) fun ω => rfl)
      (hprod σ _ fun c hc => List.mem_of_mem_filter hc)) ?_
    have hlab : ∀ (ls : List (PQ × Atom k n)), PolyMeas fun ω => (ls.map fun ℓ =>
        PFamily.op ⟨Pexp (Smat P.ψ W L)⟩ ℓ.1 (σ ℓ.2) (fun ω' =>
          ((Γ.comps.filter fun c => decide (c.label = some ℓ)).map
            (Comp.val (rbmData d P Sig W L z ω') σ)).prod) ω).prod := by
      intro ls
      induction ls with
      | nil => simpa using hL.adm_const 1
      | cons ℓ ls ih =>
        simp only [List.map_cons, List.prod_cons]
        refine hL.adm_mul _ _ ?_ ih
        have hf := hprod σ (Γ.comps.filter fun c => decide (c.label = some ℓ))
          (fun c hc => List.mem_of_mem_filter hc)
        rcases ℓ with ⟨pq, u⟩
        cases pq
        · exact hL.adm_P _ _ hf
        · have := hL.adm_add _ _ hf (hL.adm_mul _ _ (hL.adm_const (-1)) (hL.adm_P (σ u) _ hf))
          refine (congrArg PolyMeas ?_).mp this
          funext ω
          simp only [PFamily.op, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
          ring
    exact hlab _
  unfold Graph.valR
  have hsum : ∀ (A : Finset (Fin n → Zd d L)), PolyMeas fun ω =>
      ∑ s ∈ A, Γ.termR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) (Sum.elim e s) ω := by
    intro A
    induction A using Finset.induction_on with
    | empty => simpa using hL.adm_const 0
    | insert a A ha ih =>
      have := hL.adm_add _ _ (hterm (Sum.elim e a)) ih
      refine (congrArg PolyMeas ?_).mp this
      funext ω
      simp only [Pi.add_apply, Finset.sum_insert ha]
  exact hsum Finset.univ

/-! ## The large deviation events -/

section LDE

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `|G^{(x)}_{ab}| ≤ (Im z)⁻¹`. -/
private lemma QTerm_norm_greenMinor_le {z : ℂ} (hz : 0 < z.im) (ω : Sample ι) (x a b : ι) :
    ‖greenMinor (green (hmat ω) z) x a b‖ ≤ (z.im)⁻¹ := by
  have hH := hmat_isHermitian ω
  by_cases hab : a = x ∨ b = x
  · have hne := green_diag_ne_zero hH hz x
    have : greenMinor (green (hmat ω) z) x a b = 0 := by
      rcases hab with rfl | rfl <;> (unfold greenMinor; field_simp; ring)
    rw [this, norm_zero]; positivity
  · obtain ⟨ha, hb⟩ := not_or.mp hab
    rw [← minorGreen_eq_greenMinor (green (hmat ω) z) x ⟨a, ha⟩ ⟨b, hb⟩,
      ← inv_minor_resolvent hH hz x]
    have h : ‖green ((hmat ω).submatrix (Subtype.val : {c // c ≠ x} → ι) Subtype.val) z
        ⟨a, ha⟩ ⟨b, hb⟩‖ ≤ |z.im|⁻¹ := norm_green_entry_le (hH.submatrix _) hz.ne' _ _
    rw [abs_of_pos hz] at h
    exact h

/-- **The row and column large deviation bounds** at one spectral parameter: for every `p` there
is `C` such that the bounds `LDERow` and `LDECol` with factor `t` fail with probability at most
`2 |ι|² C t^{−p}`. -/
lemma QTerm_lde_prob (p : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ), S.IsSymm →
    (∀ a b, 0 ≤ S a b) → ∀ (z : ℂ), 0 < z.im → ∀ t : ℝ, 0 < t →
      gaussLaw S {ω | ¬ (LDERow (hmat ω) (green (hmat ω) z) S t ∧
          LDECol (hmat ω) (green (hmat ω) z) S t)} ≤
        ENNReal.ofReal (2 * (Fintype.card ι : ℝ) ^ 2 * (C / t ^ p)) := by
  obtain ⟨C, hC⟩ := ldeLinTail p
  refine ⟨max C 0, le_max_right _ _, fun {ι} _ _ S hS hS0 z hz t ht => ?_⟩
  have hfree : ∀ i a b, FreeOf (rowCoords i) fun ω : Sample ι => greenMinor (green (hmat ω) z) i a b :=
    fun i a b => freeOf_greenMinor z hz i a b
  have hmeas : ∀ i a b, Measurable fun ω : Sample ι => greenMinor (green (hmat ω) z) i a b :=
    fun i a b => (polyMeas_greenMinor z hz i a b).1
  -- one row
  have hrow : ∀ i j, gaussLaw S {ω | ¬ ldeRowLHS (hmat ω) (green (hmat ω) z) i j ≤
      t * ldeRowRHS S (green (hmat ω) z) i j} ≤ ENNReal.ofReal (max C 0 / t ^ p) := by
    intro i j
    have h := hC S hS hS0 i (fun ω k => greenMinor (green (hmat ω) z) i k.1 j)
      (fun k => hmeas i k.1 j) (fun k => hfree i k.1 j)
      ⟨(z.im)⁻¹, fun ω k => QTerm_norm_greenMinor_le hz ω i k.1 j⟩ t ht
    refine le_trans (measure_mono fun ω hω => ?_) (h.trans (ENNReal.ofReal_le_ofReal ?_))
    · simp only [Set.mem_ofPred_eq, not_le] at hω ⊢
      exact hω
    · exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  -- one column
  have hcol : ∀ i j, gaussLaw S {ω | ¬ ldeColLHS (hmat ω) (green (hmat ω) z) i j ≤
      t * ldeColRHS S (green (hmat ω) z) i j} ≤ ENNReal.ofReal (max C 0 / t ^ p) := by
    intro i j
    have h := hC S hS hS0 i (fun ω k => star (greenMinor (green (hmat ω) z) i j k.1))
      (fun k => Complex.continuous_conj.measurable.comp (hmeas i j k.1)) (fun k ω η => by simp only [hfree i j k.1 ω η])
      ⟨(z.im)⁻¹, fun ω k => by rw [norm_star]; exact QTerm_norm_greenMinor_le hz ω i j k.1⟩ t ht
    refine le_trans (measure_mono fun ω hω => ?_) (h.trans (ENNReal.ofReal_le_ofReal ?_))
    · simp only [Set.mem_ofPred_eq, not_le] at hω ⊢
      have e1 : ‖∑ k : {a : ι // a ≠ i}, hmat ω i k.1 *
          star (greenMinor (green (hmat ω) z) i j k.1)‖ =
          ‖∑ k : {a : ι // a ≠ i}, greenMinor (green (hmat ω) z) i j k.1 * hmat ω k.1 i‖ := by
        rw [← norm_star, star_sum]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [star_mul', star_star]
        have : star (hmat ω i k.1) = hmat ω k.1 i := by
          have := congrFun (congrFun (hmat_isHermitian ω) k.1) i
          simpa [Matrix.conjTranspose_apply] using this
        rw [this, mul_comm]
      have e2 : ∑ k : {a : ι // a ≠ i}, S i k.1 * ‖star (greenMinor (green (hmat ω) z) i j k.1)‖ ^ 2
          = ldeColRHS S (green (hmat ω) z) i j := by
        unfold ldeColRHS; simp only [norm_star]
      rw [e1, e2]
      exact hω
    · exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  have hsub : {ω : Sample ι | ¬ (LDERow (hmat ω) (green (hmat ω) z) S t ∧
      LDECol (hmat ω) (green (hmat ω) z) S t)} ⊆
      (⋃ ij : ι × ι, {ω | ¬ ldeRowLHS (hmat ω) (green (hmat ω) z) ij.1 ij.2 ≤
        t * ldeRowRHS S (green (hmat ω) z) ij.1 ij.2}) ∪
      ⋃ ij : ι × ι, {ω | ¬ ldeColLHS (hmat ω) (green (hmat ω) z) ij.1 ij.2 ≤
        t * ldeColRHS S (green (hmat ω) z) ij.1 ij.2} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, LDERow, LDECol, not_and_or, not_forall] at hω
    rcases hω with ⟨i, j, h⟩ | ⟨i, j, h⟩
    · exact Or.inl (Set.mem_iUnion.2 ⟨(i, j), h⟩)
    · exact Or.inr (Set.mem_iUnion.2 ⟨(i, j), h⟩)
  have hC0 : 0 ≤ max C 0 / t ^ p := by positivity
  calc gaussLaw S _ ≤ gaussLaw S ((⋃ ij : ι × ι, {ω | ¬ ldeRowLHS (hmat ω) (green (hmat ω) z)
        ij.1 ij.2 ≤ t * ldeRowRHS S (green (hmat ω) z) ij.1 ij.2}) ∪
        ⋃ ij : ι × ι, {ω | ¬ ldeColLHS (hmat ω) (green (hmat ω) z) ij.1 ij.2 ≤
          t * ldeColRHS S (green (hmat ω) z) ij.1 ij.2}) := measure_mono hsub
    _ ≤ (∑ ij : ι × ι, ENNReal.ofReal (max C 0 / t ^ p)) +
          ∑ ij : ι × ι, ENNReal.ofReal (max C 0 / t ^ p) := by
        refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
        · exact (measure_iUnion_fintype_le _ _).trans
            (Finset.sum_le_sum fun ij _ => hrow ij.1 ij.2)
        · exact (measure_iUnion_fintype_le _ _).trans
            (Finset.sum_le_sum fun ij _ => hcol ij.1 ij.2)
    _ = ENNReal.ofReal (2 * (Fintype.card ι : ℝ) ^ 2 * (max C 0 / t ^ p)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
          ← two_mul, ← mul_assoc]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
        congr 1
        rw [ENNReal.ofReal_ofNat, ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        push_cast; ring

end LDE

section Resampled

variable {ι : Type} [Fintype ι] [DecidableEq ι]

end Resampled

/-! ## Dotted blocks -/

section Blocks

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
private lemma QTerm_flatten_map_singleton (as : List V) : (as.map fun a => [a]).flatten = as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

private lemma QTerm_joinBlocks_flatten_perm (P : List (List V)) (u v : V) :
    (joinBlocks P u v).flatten.Perm P.flatten := by
  unfold joinBlocks
  rw [List.flatten_append, List.flatten_singleton]
  have h := (List.filter_append_perm (fun B : List V => B.contains u || B.contains v) P).flatten
  rw [List.flatten_append] at h
  exact List.perm_append_comm.trans h

/-- One step of `dotBlocks`. -/
private def QTerm_blockStep (c : Comp V) (P : List (List V)) : List (List V) :=
  if c.kind = .dot then joinBlocks P c.x c.y else P

private lemma QTerm_dotBlocks_snoc (as : List V) (cs : List (Comp V)) (c : Comp V) :
    dotBlocks as (cs ++ [c]) = QTerm_blockStep c (dotBlocks as cs) := by
  simp [dotBlocks, List.foldl_append, QTerm_blockStep]

private lemma QTerm_dotBlocks_nil (as : List V) : dotBlocks as ([] : List (Comp V)) =
    as.map fun a => [a] := rfl

private lemma QTerm_dotBlocks_flatten_perm (as : List V) (cs : List (Comp V)) :
    (dotBlocks as cs).flatten.Perm as := by
  induction cs using List.reverseRecOn with
  | nil => rw [QTerm_dotBlocks_nil, QTerm_flatten_map_singleton]
  | append_singleton cs c ih =>
    rw [QTerm_dotBlocks_snoc, QTerm_blockStep]
    split_ifs
    · exact (QTerm_joinBlocks_flatten_perm _ _ _).trans ih
    · exact ih

/-- The two ends of a dotted edge lie in one block. -/
private lemma QTerm_dotBlocks_joined (as : List V) (cs : List (Comp V))
    (hcs : ∀ c ∈ cs, c.x ∈ as ∧ c.y ∈ as) :
    ∀ c ∈ cs, c.kind = .dot → ∃ B ∈ dotBlocks as cs, c.x ∈ B ∧ c.y ∈ B := by
  induction cs using List.reverseRecOn with
  | nil => intro c hc; simp at hc
  | append_singleton cs c ih =>
    have ih' := ih fun c' hc' => hcs c' (List.mem_append_left _ hc')
    intro c' hc' hk'
    rw [QTerm_dotBlocks_snoc, QTerm_blockStep]
    have hmem : ∀ a ∈ as, ∃ B ∈ dotBlocks as cs, a ∈ B := by
      intro a ha
      have := (QTerm_dotBlocks_flatten_perm as cs).mem_iff.2 ha
      rwa [List.mem_flatten] at this
    split_ifs with hk
    · rcases List.mem_append.1 hc' with hc' | hc'
      · obtain ⟨B, hB, hx, hy⟩ := ih' c' hc' hk'
        by_cases hcB : (B.contains c.x || B.contains c.y) = true
        · refine ⟨(dotBlocks as cs |>.filter fun B => B.contains c.x || B.contains c.y).flatten,
            ?_, ?_, ?_⟩
          · unfold joinBlocks
            exact List.mem_append_right _ (List.mem_singleton_self _)
          · rw [List.mem_flatten]
            exact ⟨B, List.mem_filter.2 ⟨hB, hcB⟩, hx⟩
          · rw [List.mem_flatten]
            exact ⟨B, List.mem_filter.2 ⟨hB, hcB⟩, hy⟩
        · refine ⟨B, ?_, hx, hy⟩
          unfold joinBlocks
          refine List.mem_append_left _ (List.mem_filter.2 ⟨hB, ?_⟩)
          simpa using hcB
      · rw [List.mem_singleton] at hc'
        subst hc'
        obtain ⟨hxa, hya⟩ := hcs _ (List.mem_append_right _ (List.mem_singleton_self _))
        obtain ⟨B₁, hB₁, hx⟩ := hmem _ hxa
        obtain ⟨B₂, hB₂, hy⟩ := hmem _ hya
        refine ⟨(dotBlocks as cs |>.filter fun B => B.contains c'.x || B.contains c'.y).flatten,
          ?_, ?_, ?_⟩
        · unfold joinBlocks
          exact List.mem_append_right _ (List.mem_singleton_self _)
        · rw [List.mem_flatten]
          exact ⟨B₁, List.mem_filter.2 ⟨hB₁, by simp [hx]⟩, hx⟩
        · rw [List.mem_flatten]
          exact ⟨B₂, List.mem_filter.2 ⟨hB₂, by simp [hy]⟩, hy⟩
    · rcases List.mem_append.1 hc' with hc' | hc'
      · exact ih' c' hc' hk'
      · rw [List.mem_singleton] at hc'
        subst hc'
        exact absurd hk' hk

omit [DecidableEq V] in
/-- Reachability in the graph of a relation is the equivalence generated by it. -/
private lemma QTerm_reachable_fromRel_iff (r : V → V → Prop) (u v : V) :
    (SimpleGraph.fromRel r).Reachable u v ↔ Relation.EqvGen r u v := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact Relation.EqvGen.refl _
    | cons hadj _ ih =>
      rw [SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with h | h
      · exact (Relation.EqvGen.rel _ _ h).trans _ _ _ ih
      · exact (Relation.EqvGen.rel _ _ h).symm.trans _ _ _ ih
  · intro h
    induction h with
    | rel a b hab =>
      by_cases hne : a = b
      · rw [hne]
      · exact ((SimpleGraph.fromRel_adj _ _ _).2 ⟨hne, Or.inl hab⟩).reachable
    | refl a => exact SimpleGraph.Reachable.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

end Blocks

private lemma QTerm_mem_allAtoms {k n : ℕ} (u : Atom k n) : u ∈ allAtoms k n := by
  rcases u with a | b <;> simp [allAtoms]

private lemma QTerm_allAtoms_nodup {k n : ℕ} : (allAtoms k n).Nodup := by
  unfold allAtoms
  refine List.Nodup.append ((List.nodup_finRange k).map Sum.inl_injective)
    ((List.nodup_finRange n).map Sum.inr_injective) ?_
  simp [List.disjoint_left]

/-- An atom lies in at most one block. -/
private lemma QTerm_block_unique {k n : ℕ} (cs : List (Comp (Atom k n))) {B₁ B₂ : List (Atom k n)}
    (h₁ : B₁ ∈ dotBlocks (allAtoms k n) cs) (h₂ : B₂ ∈ dotBlocks (allAtoms k n) cs)
    {v : Atom k n} (hv₁ : v ∈ B₁) (hv₂ : v ∈ B₂) : B₁ = B₂ := by
  have hnd : (dotBlocks (allAtoms k n) cs).flatten.Nodup :=
    (QTerm_dotBlocks_flatten_perm _ cs).nodup_iff.2 QTerm_allAtoms_nodup
  rw [List.nodup_flatten] at hnd
  by_contra hne
  have := hnd.2.forall h₁ h₂ hne
  exact this hv₁ hv₂

/-- Two atoms joined by a path of dotted edges lie in one block. -/
private lemma QTerm_mem_block_of_sameBlock {k n : ℕ} (Γ : Graph k n) {u v : Atom k n}
    (h : Γ.SameBlock u v) : ∃ B ∈ dotBlocks (allAtoms k n) Γ.comps, u ∈ B ∧ v ∈ B := by
  unfold Graph.SameBlock Graph.dotGraph at h
  rw [QTerm_reachable_fromRel_iff] at h
  induction h with
  | rel a b hab =>
    obtain ⟨c, hc, hk, rfl, rfl⟩ := hab
    exact QTerm_dotBlocks_joined _ _ (fun c _ => ⟨QTerm_mem_allAtoms _, QTerm_mem_allAtoms _⟩)
      c hc hk
  | refl a =>
    have := (QTerm_dotBlocks_flatten_perm (allAtoms k n) Γ.comps).mem_iff.2
      (QTerm_mem_allAtoms a)
    rw [List.mem_flatten] at this
    obtain ⟨B, hB, ha⟩ := this
    exact ⟨B, hB, ha, ha⟩
  | symm a b _ ih =>
    obtain ⟨B, hB, ha, hb⟩ := ih
    exact ⟨B, hB, hb, ha⟩
  | trans a b c _ _ ih1 ih2 =>
    obtain ⟨B₁, hB₁, ha, hb⟩ := ih1
    obtain ⟨B₂, hB₂, hb', hc⟩ := ih2
    obtain rfl := QTerm_block_unique Γ.comps hB₁ hB₂ hb hb'
    exact ⟨B₁, hB₁, ha, hc⟩

/-! ## The graphs of `Q` -/

section QGraphs

/-- In a graph that is not a `⊕`-recollision graph at `𝔟₁ = 𝔟₂`, the atoms `⊕` and `⊖` are not
identified with an internal atom. -/
private lemma QTerm_unpinned_pm {n : ℕ} (g : Graph 3 n) (hD : ¬ g.DiagRecoll) (j : Fin 3)
    (hj : j = 1 ∨ j = 2) : g.Unpinned (.inl j) := by
  refine ⟨rfl, fun b hb => hD ?_⟩
  obtain ⟨B, hB, h1, h2⟩ := QTerm_mem_block_of_sameBlock g hb
  unfold Graph.DiagRecoll
  rw [List.any_eq_true]
  refine ⟨B, hB, ?_⟩
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.contains_iff_mem]
  rcases hj with rfl | rfl
  · exact ⟨Or.inl h1, .inr b, h2, rfl⟩
  · exact ⟨Or.inr h1, .inr b, h2, rfl⟩

/-- Two distinct members of a list give length at least `2`. -/
private lemma QTerm_two_le_length {α : Type*} {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : 2 ≤ l.length := by
  rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
  · simp at ha
  · simp only [List.mem_singleton] at ha hb; exact absurd (ha.trans hb.symm) hab
  · simp

/-- **The label atom is internal**: a `Q`-graph with an internal atom that is not a
`⊕`-recollision graph at `𝔟₁ = 𝔟₂`, with [II, Def 6.3 (3)] (`Graph.QLabelInMISB`), the clause on
the external atoms and the rooting at the external atoms, has its label at an internal atom (an
external label atom `⊕` or `⊖` would carry two components other than dotted edges). -/
lemma QTerm_label_internal {n : ℕ} (g : Graph 3 n) (hn : n ≠ 0) (hD : ¬ g.DiagRecoll)
    (hQ : g.QLabelInMISB) (hE : g.ExtClause) (hR : g.RootedAtExt) (u : Atom 3 n)
    (hu : ∃ c ∈ g.comps, c.label = some (.Q, u)) : ∃ α : Fin n, u = .inr α := by
  rcases u with j | α
  · exfalso
    obtain ⟨c, hc, hl⟩ := hu
    rcases hQ c hc (.inl j) hl with hM | ⟨hj, hn0 | ⟨c', hc', a, ⟨w, hw⟩, hends, -⟩⟩
    · have hint : g.molRep (.inl j) ∈ g.toMG'.int := by
        simp only [MGraph.MIS, Finset.mem_filter] at hM; exact hM.1
      simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and] at hint
      obtain ⟨b, hb⟩ := hint
      simp [Graph.molRep] at hb
    · exact hn hn0
    · have hfilt : ∀ c₂ ∈ g.comps, (c₂.x = .inl j ∨ c₂.y = .inl j) → c₂.kind ≠ .dot →
          c₂.kind ≠ .xdot → c₂ ∈ g.comps.filter fun c => decide ((c.x = .inl j ∨ c.y = .inl j) ∧
            c.kind ≠ .dot ∧ c.kind ≠ .xdot) := fun c₂ h1 h2 h3 h4 =>
        List.mem_filter.2 ⟨h1, by simp [h2, h3, h4]⟩
      have hc'm := hfilt c' hc' (by rcases hends with h | h; exact Or.inl h.1; exact Or.inr h.2)
        (by rw [hw]; simp) (by rw [hw]; simp)
      rcases hj with hj | hj
      · obtain rfl : j = 1 := Sum.inl_injective hj
        have hun := QTerm_unpinned_pm g hD 1 (Or.inl rfl)
        obtain ⟨hex, -, hdeg⟩ := hE.2.2.2.2 hun
        obtain ⟨c₂, hc₂, hk₂, hat₂⟩ : ∃ c₂ ∈ g.comps, (c₂.kind = .G .plus ∨
            c₂.kind.isDiffusive = true) ∧ (c₂.x = .inl 1 ∨ c₂.y = .inl 1) := by
          rcases hex with ⟨c₂, hc₂, hk, hat⟩ | ⟨c₂, hc₂, hk, hat⟩
          · exact ⟨c₂, hc₂, Or.inl hk, hat⟩
          · exact ⟨c₂, hc₂, Or.inr hk, by
              rcases hat with h | h
              · exact Or.inl h.1
              · exact Or.inr h.1⟩
        have hk2 : c₂.kind ≠ .dot ∧ c₂.kind ≠ .xdot := by
          rcases hk₂ with h | h <;> constructor <;> intro h' <;> rw [h'] at h <;>
            simp [Kind.isDiffusive] at h
        have hc2m := hfilt c₂ hc₂ hat₂ hk2.1 hk2.2
        have hne : c' ≠ c₂ := by
          intro he; rw [← he, hw] at hk₂; rcases hk₂ with h | h <;> simp [Kind.isDiffusive] at h
        have := QTerm_two_le_length hc'm hc2m hne
        unfold Graph.nonDotDeg at hdeg
        omega
      · obtain rfl : j = 2 := Sum.inl_injective hj
        have hun := QTerm_unpinned_pm g hD 2 (Or.inr rfl)
        obtain ⟨hnodiff, hdeg⟩ := hE.2.2.2.1 hun
        obtain ⟨c₂, hc₂, hk₂, hat₂⟩ : ∃ c₂ ∈ g.comps, c₂.kind = .G .minus ∧
            (c₂.x = .inl 2 ∨ c₂.y = .inl 2) := by
          rcases hR.2.2 with ⟨c₂, hc₂, hk, hat⟩ | ⟨c₂, hc₂, hk, hat⟩
          · exact ⟨c₂, hc₂, hk, by rcases hat with h | h; exact Or.inl h.1; exact Or.inr h.1⟩
          · exfalso
            have := hnodiff c₂ hc₂ hk
            rcases hat with h | h
            · exact this.1 h.1
            · exact this.2 h.1
        have hc2m := hfilt c₂ hc₂ hat₂ (by rw [hk₂]; simp) (by rw [hk₂]; simp)
        have hne : c' ≠ c₂ := by intro he; rw [← he, hw] at hk₂; cases hk₂
        have := QTerm_two_le_length hc'm hc2m hne
        unfold Graph.nonDotDeg at hdeg
        omega
  · exact ⟨α, rfl⟩

end QGraphs

section Count

end Count

section Elem

variable {ι : Type} [Fintype ι] [DecidableEq ι]

end Elem

section SliceGen

end SliceGen

section Rooted

variable {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ) [NeZero L] (z : ℂ)

variable {P Sig W L z}

end Rooted

section Setting

variable {d : ℕ} {P : Profile d} {c₀ c₁ κ ε c₀T : ℝ} {n D : ℕ} {Sig : ℕ → Expansion 2}
  {𝒯 : TRec} {ε₀ : ℝ} {U : SizeL → Type} {z : ∀ p, U p → ℂ} {Φ : ∀ p, U p → ℝ} {δ : ℝ}

end Setting

section Instances

set_option maxRecDepth 100000

section Witness

open scoped FourierTransform SchwartzMap Nat ContDiff

end Witness

end Instances

end RBM8D
