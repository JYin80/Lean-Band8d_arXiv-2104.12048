module

public import RBM8D.Diffusion.Defs
public import RBM8D.TExp.Closure
public import RBM8D.Kernel.PropagatorSymbol
public import RBM8D.Prob.Partial

@[expose] public section

/-!
# Translation invariance of the Gaussian model

`modelTransInv : modelTransInvStmt`: on `Z_L^d`, wherever the variance matrix `S_{W,L}` of
[I, Assumption 1.1] is symmetric, the matrices `E T_{xy}` ([I, (1.21)]), `E |G_{xy}|²`, the local
correction `𝒢` ([I, (8.16)]) and the error `E(Γ_A + Γ_Err)` ([I, (8.15), (8.20)]) are
translation invariant, for every family of self-energies and every `T`-equation. This is the
invariance that makes them circulant in [I, (1.35)–(1.36)].

* The sample `ω` is a family of real coordinates, one per diagonal entry and two per oriented
  off-diagonal pair, the orientation being given by an injective key. A translation `x ↦ x + a`
  permutes the pairs, and reverses the orientation of some of them; the map `T_a` on samples with
  `H(T_a ω)_{xy} = H(ω)_{x+a, y+a}` permutes the coordinates and changes the sign of the
  imaginary part of a reversed pair.
* `T_a` preserves the Gaussian law, because the variance of the reversed pair is `s_{y x}`, which
  is `s_{xy}` for symmetric `S`, and a centred Gaussian is invariant under `x ↦ −x`.
* The resolvent, its minors, the components of a graph, the partial expectations `P_x` and the
  values of the labelled graphs are covariant: `T_a` composed with them moves every atom by `a`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open MeasureTheory ProbabilityTheory Complex Matrix
open scoped BigOperators NNReal

namespace RBM8D

open Graphs

namespace ModelSymm

/-! ## The action of a permutation of the index set on samples -/

section Coords

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The pair `(a, b)` ordered by the key. -/
private def ordPair (a b : ι) : ι × ι :=
  if idxKey ι a < idxKey ι b then (a, b) else (b, a)

/-- The ordered pair of two distinct indices is oriented by the key. -/
private lemma ordPair_lt {a b : ι} (h : a ≠ b) :
    idxKey ι (ordPair a b).1 < idxKey ι (ordPair a b).2 := by
  have hne : idxKey ι a ≠ idxKey ι b := fun h' => h (idxKey_injective h')
  unfold ordPair
  split_ifs with h1
  · exact h1
  · exact lt_of_le_of_ne (not_lt.1 h1) (Ne.symm hne)

/-- The two indices of an oriented off-diagonal pair are distinct. -/
private lemma offPair_ne (p : OffPair ι) : p.1.1 ≠ p.1.2 := fun h => by
  have := p.2
  rw [h] at this
  exact lt_irrefl _ this

/-- The permutation of the coordinates induced by a permutation `e` of the index set: the pair
`(x, y)` goes to the pair `{e x, e y}` ordered by the key. -/
private def tauFun (e : ι ≃ ι) : Coord ι → Coord ι
  | .inl x => .inl (e x)
  | .inr (p, b) =>
    .inr (⟨ordPair (e p.1.1) (e p.1.2), ordPair_lt fun h => offPair_ne p (e.injective h)⟩, b)

/-- The sign of a coordinate: `−1` on the imaginary part of a pair whose orientation is reversed
by `e`. -/
private def sgnFun (e : ι ≃ ι) : Coord ι → ℝ
  | .inl _ => 1
  | .inr (p, b) => if b = false ∧ ¬ idxKey ι (e p.1.1) < idxKey ι (e p.1.2) then -1 else 1

/-- The action of `e` on samples. -/
private def Tm (e : ι ≃ ι) (ω : Sample ι) : Sample ι := fun c => sgnFun e c * ω (tauFun e c)

/-- The permutation of the coordinates is injective. -/
private lemma tauFun_injective (e : ι ≃ ι) : Function.Injective (tauFun e) := by
  rintro (x | ⟨⟨⟨x, y⟩, hxy⟩, b⟩) (x' | ⟨⟨⟨x', y'⟩, hxy'⟩, b'⟩) h
  · simp only [tauFun, Sum.inl.injEq] at h
    rw [e.injective h]
  · simp [tauFun] at h
  · simp [tauFun] at h
  · simp only [tauFun, Sum.inr.injEq, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, rfl⟩ := h
    simp only [ordPair] at h1
    have k1 : idxKey ι x < idxKey ι y := hxy
    have k2 : idxKey ι x' < idxKey ι y' := hxy'
    split_ifs at h1 with c1 c2 c2 <;> simp only [Prod.mk.injEq] at h1 <;>
      obtain ⟨h2, h3⟩ := h1 <;> have h2' := e.injective h2 <;> have h3' := e.injective h3 <;>
      subst h2' h3'
    all_goals first | rfl | (exfalso; omega)

/-- `tauFun e` as a permutation of the coordinates. -/
private def tauEquiv (e : ι ≃ ι) : Coord ι ≃ Coord ι :=
  Equiv.ofBijective (tauFun e) (tauFun_injective e).bijective_of_finite

/-- `tauEquiv e` is `tauFun e`. -/
private lemma tauEquiv_apply (e : ι ≃ ι) (c : Coord ι) : tauEquiv e c = tauFun e c := rfl

/-- The entries of `H(T_e ω)` are those of `H(ω)` at `e x, e y`. -/
private lemma hmat_Tm (e : ι ≃ ι) (ω : Sample ι) (x y : ι) :
    hmat (Tm e ω) x y = hmat ω (e x) (e y) := by
  rcases lt_trichotomy (idxKey ι x) (idxKey ι y) with h | h | h
  · have hne : e x ≠ e y := fun h' => by
      have := e.injective h'
      subst this
      exact lt_irrefl _ h
    have hk : idxKey ι (e x) ≠ idxKey ι (e y) := fun h' => hne (idxKey_injective h')
    by_cases h1 : idxKey ι (e x) < idxKey ι (e y)
    · simp [hmat, h, h1, Tm, tauFun, sgnFun, ordPair]
    · have h2 : idxKey ι (e y) < idxKey ι (e x) := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm hk)
      simp [hmat, h, h1, h2, h2.le, Tm, tauFun, sgnFun, ordPair, sub_eq_add_neg]
  · obtain rfl := idxKey_injective h
    simp [hmat, Tm, tauFun, sgnFun]
  · have hne : e x ≠ e y := fun h' => by
      have := e.injective h'
      subst this
      exact lt_irrefl _ h
    have hk : idxKey ι (e x) ≠ idxKey ι (e y) := fun h' => hne (idxKey_injective h')
    by_cases h1 : idxKey ι (e y) < idxKey ι (e x)
    · have h2 : ¬ idxKey ι (e x) < idxKey ι (e y) := lt_asymm h1
      simp [hmat, h, lt_asymm h, h1, h2, Tm, tauFun, sgnFun, ordPair]
    · have h2 : idxKey ι (e x) < idxKey ι (e y) := lt_of_le_of_ne (not_lt.1 h1) hk
      simp [hmat, h, lt_asymm h, h1, h2, h2.le, Tm, tauFun, sgnFun, ordPair, sub_eq_add_neg]

end Coords

/-! ## The law is invariant -/

section Law

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A permutation of the index set that preserves a symmetric variance matrix preserves the
variance of the coordinates. -/
private lemma coordVar_tau (S : Matrix ι ι ℝ) (e : ι ≃ ι) (hSe : ∀ x y, S (e x) (e y) = S x y)
    (hSs : ∀ x y, S x y = S y x) (c : Coord ι) : coordVar S (tauFun e c) = coordVar S c := by
  rcases c with x | ⟨p, b⟩
  · simp [coordVar, tauFun, hSe]
  · simp only [coordVar, tauFun, ordPair]
    split_ifs
    · rw [hSe]
    · rw [hSe, hSs]

/-- A sign is `1` or `−1`. -/
private lemma sgnFun_cases (e : ι ≃ ι) (c : Coord ι) : sgnFun e c = 1 ∨ sgnFun e c = -1 := by
  rcases c with x | ⟨p, b⟩
  · exact Or.inl rfl
  · simp only [sgnFun]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- The action of `e` on samples preserves the Gaussian law of the model. -/
private lemma mp_Tm (S : Matrix ι ι ℝ) (e : ι ≃ ι) (hSe : ∀ x y, S (e x) (e y) = S x y)
    (hSs : ∀ x y, S x y = S y x) : MeasurePreserving (Tm e) (gaussLaw S) (gaussLaw S) := by
  have hF : MeasurePreserving (MeasurableEquiv.arrowCongr' (tauEquiv e).symm
      (MeasurableEquiv.refl ℝ)) (gaussLaw S) (gaussLaw S) := by
    refine measurePreserving_arrowCongr' (fun c => gaussianReal 0 (coordVar S c))
      (fun c => gaussianReal 0 (coordVar S c)) (tauEquiv e).symm (MeasurableEquiv.refl ℝ)
      fun c => ?_
    have := coordVar_tau S e hSe hSs ((tauEquiv e).symm c)
    rw [← tauEquiv_apply, Equiv.apply_symm_apply] at this
    rw [this]
    exact MeasurePreserving.id _
  have hG : MeasurePreserving (fun (ω : Sample ι) (c : Coord ι) => sgnFun e c * ω c)
      (gaussLaw S) (gaussLaw S) := by
    refine measurePreserving_pi (fun c => gaussianReal 0 (coordVar S c))
      (fun c => gaussianReal 0 (coordVar S c)) (f := fun c x => sgnFun e c * x) fun c => ?_
    rcases sgnFun_cases e c with h | h
    · simp only [h, one_mul]
      exact MeasurePreserving.id _
    · simp only [h, neg_one_mul]
      refine ⟨measurable_neg, ?_⟩
      simpa using gaussianReal_map_neg (μ := 0) (v := coordVar S c)
  have h := hG.comp hF
  have e1 : Tm e = (fun (ω : Sample ι) (c : Coord ι) => sgnFun e c * ω c) ∘
      ⇑(MeasurableEquiv.arrowCongr' (tauEquiv e).symm (MeasurableEquiv.refl ℝ)) := by
    funext ω c
    rfl
  rw [e1]
  exact h

/-- The action of `e` on samples is injective. -/
private lemma Tm_injective (e : ι ≃ ι) : Function.Injective (Tm e) := by
  intro ω ω' h
  funext c'
  obtain ⟨c, rfl⟩ := (tauEquiv e).surjective c'
  have h1 := congrFun h c
  change sgnFun e c * ω (tauFun e c) = sgnFun e c * ω' (tauFun e c) at h1
  change ω (tauFun e c) = ω' (tauFun e c)
  rcases sgnFun_cases e c with hs | hs <;> rw [hs] at h1 <;> linarith

/-- Integrals against the Gaussian law of the model are invariant under the action of `e`. -/
private lemma integral_Tm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Matrix ι ι ℝ)
    (e : ι ≃ ι) (hSe : ∀ x y, S (e x) (e y) = S x y) (hSs : ∀ x y, S x y = S y x)
    (g : Sample ι → E) : ∫ ω, g (Tm e ω) ∂(gaussLaw S) = ∫ ω, g ω ∂(gaussLaw S) :=
  (mp_Tm S e hSe hSs).integral_comp
    ((mp_Tm S e hSe hSs).measurable.measurableEmbedding (Tm_injective e)) g

/-- The coordinates of row and column `x`. -/
private lemma mem_rowCoords (x : ι) (c : Coord ι) : c ∈ rowCoords x ↔
    (match c with | .inl x' => x' = x | .inr (p, _) => p.1.1 = x ∨ p.1.2 = x) := by
  rcases c with x' | ⟨p, b⟩
  · simp only [rowCoords, entryCoords, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨y, h, -⟩
      exact h
    · intro h
      exact ⟨x', h, rfl⟩
  · simp only [rowCoords, entryCoords, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨y, h | h⟩
      · exact Or.inl h.1
      · exact Or.inr h.2
    · rintro (h | h)
      · exact ⟨p.1.2, Or.inl ⟨h, rfl⟩⟩
      · exact ⟨p.1.1, Or.inr ⟨rfl, h⟩⟩

/-- The action of `e` maps the coordinates of row `x` to those of row `e x`. -/
private lemma tau_mem_rowCoords (e : ι ≃ ι) (x : ι) (c : Coord ι) :
    tauFun e c ∈ rowCoords (e x) ↔ c ∈ rowCoords x := by
  rw [mem_rowCoords, mem_rowCoords]
  rcases c with x' | ⟨p, b⟩
  · simp only [tauFun, e.injective.eq_iff]
  · simp only [tauFun, ordPair]
    split_ifs
    · simp only [e.injective.eq_iff]
    · simp only [e.injective.eq_iff, or_comm]

/-- Overwriting the coordinates of row `x` commutes with the action of `e`. -/
private lemma piecewise_Tm (e : ι ≃ ι) (x : ι) (η ω : Sample ι) :
    (rowCoords x).piecewise (Tm e η) (Tm e ω) = Tm e ((rowCoords (e x)).piecewise η ω) := by
  funext c
  by_cases h : c ∈ rowCoords x
  · have h' : tauFun e c ∈ rowCoords (e x) := (tau_mem_rowCoords e x c).2 h
    simp only [Finset.piecewise_eq_of_mem _ _ _ h, Tm, Finset.piecewise_eq_of_mem _ _ _ h']
  · have h' : tauFun e c ∉ rowCoords (e x) := fun hh => h ((tau_mem_rowCoords e x c).1 hh)
    simp only [Finset.piecewise_eq_of_notMem _ _ _ h, Tm, Finset.piecewise_eq_of_notMem _ _ _ h']

/-- The partial expectation `P_x` is covariant under the action of `e`. -/
private lemma Pexp_Tm (S : Matrix ι ι ℝ) (e : ι ≃ ι) (hSe : ∀ x y, S (e x) (e y) = S x y)
    (hSs : ∀ x y, S x y = S y x) (x : ι) (f f' : Sample ι → ℂ) (hf : ∀ ω, f (Tm e ω) = f' ω)
    (ω : Sample ι) : Pexp S x f (Tm e ω) = Pexp S (e x) f' ω := by
  unfold Pexp partialExp
  rw [← integral_Tm S e hSe hSs (fun η => f ((rowCoords x).piecewise η (Tm e ω)))]
  simp only [piecewise_Tm, hf]

end Law

/-! ## Covariance of the data record and of the graph values -/

section Cov

variable {d L : ℕ} [NeZero L]

/-- The resolvent at the translated sample is the translated resolvent. -/
private lemma green_Tm (a : Zd d L) (z : ℂ) (ω : Sample (Zd d L)) (x y : Zd d L) :
    green (hmat (Tm (Equiv.addRight a) ω)) z x y = green (hmat ω) z (x + a) (y + a) := by
  have h : hmat (Tm (Equiv.addRight a) ω) - z • (1 : Matrix (Zd d L) (Zd d L) ℂ) =
      (hmat ω - z • 1).submatrix (Equiv.addRight a) (Equiv.addRight a) := by
    ext u v
    simp only [hmat_Tm, Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply,
      Matrix.one_apply, Equiv.coe_addRight, add_left_inj]
  unfold green
  rw [h, Matrix.inv_submatrix_equiv]
  rfl

/-- The minor of a translated list of atoms is the translate of the minor. -/
private lemma toFinset_map_add {V : Type*} (a : Zd d L) (σ : V → Zd d L) (l : List V) :
    (l.map fun v => σ v + a).toFinset = (l.map σ).toFinset.image (· + a) := by
  ext u
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨σ v, ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, rfl⟩

/-- A finset is a singleton iff its translate is. -/
private lemma exists_image_singleton (a : Zd d L) (U : Finset (Zd d L)) :
    (∃ y, U.image (· + a) = {y}) ↔ ∃ x, U = {x} := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y - a, ?_⟩
    have h := congrArg (Finset.image (· - a)) hy
    rw [Finset.image_image, Finset.image_singleton] at h
    have e1 : ((fun x : Zd d L => x - a) ∘ fun x => x + a) = id := by
      funext x
      simp
    rw [e1, Finset.image_id] at h
    exact h
  · rintro ⟨x, rfl⟩
    exact ⟨x + a, Finset.image_singleton _ _⟩

variable (P : Profile d) (Sig : ℕ → Expansion 2) (W : ℕ) (z : ℂ)

/-- The resolvent minors of the data record at the translated sample. -/
private lemma gm_Tm (a : Zd d L) (U : Finset (Zd d L)) (ω : Sample (Zd d L)) (p q : Zd d L) :
    (rbmData d P Sig W L z (Tm (Equiv.addRight a) ω)).Gm U p q =
      (rbmData d P Sig W L z ω).Gm (U.image (· + a)) (p + a) (q + a) := by
  change (if h : ∃ x, U = {x} then Matrix.of (greenMinor (green (hmat (Tm (Equiv.addRight a) ω)) z)
      h.choose) else green (hmat (Tm (Equiv.addRight a) ω)) z) p q =
    (if h : ∃ x, U.image (· + a) = {x} then Matrix.of (greenMinor (green (hmat ω) z) h.choose)
      else green (hmat ω) z) (p + a) (q + a)
  split_ifs with h h2 h2
  · have hc : ∀ x, U = {x} → h.choose = x := fun x hx =>
      (Finset.singleton_inj.1 (hx.symm.trans h.choose_spec)).symm
    obtain ⟨x, hx⟩ := h
    have hc1 := hc x hx
    have hc2 : h2.choose = x + a := by
      have h3 : Finset.image (· + a) U = {x + a} := by rw [hx, Finset.image_singleton]
      have := h3.symm.trans h2.choose_spec
      exact (Finset.singleton_inj.1 this).symm
    rw [hc1, hc2]
    simp only [Matrix.of_apply, greenMinor, green_Tm]
  · exact absurd ((exists_image_singleton a U).2 h) h2
  · exact absurd ((exists_image_singleton a U).1 h2) h
  · exact green_Tm a z ω p q

/-! ### The deterministic fields are translation invariant -/

/-- The complexification of a translation invariant kernel is translation invariant. -/
private lemma transInv_map_ofReal (S : Matrix (Zd d L) (Zd d L) ℝ) (hS : TransInv S) :
    TransInv (S.map fun r => (r : ℂ)) := fun x y a => by
  simp only [Matrix.map_apply, hS x y a]

/-- A scalar multiple of a translation invariant kernel is translation invariant. -/
private lemma transInv_smul_c (w : ℂ) {K : Matrix (Zd d L) (Zd d L) ℂ} (hK : TransInv K) :
    TransInv (w • K) := fun x y a => by
  simp only [Matrix.smul_apply, hK x y a]

/-- `K (1 − K)⁻¹` is translation invariant for translation invariant `K`. -/
private lemma transInv_mul_inv_one_sub (K : Matrix (Zd d L) (Zd d L) ℂ) (hK : TransInv K) :
    TransInv (K * (1 - K)⁻¹) := by
  have h1 : TransInv (1 - K) := fun x y a => by
    simp only [Matrix.sub_apply, Matrix.one_apply, add_left_inj, hK x y a]
  rw [Matrix.nonsing_inv_eq_ringInverse]
  exact TransInv_mul _ _ hK (TransInv_ringInverse _ h1)

/-- A kernel on `Z_L^d` invariant under translations and under the reflection `x ↦ −x`. -/
private def SK (M : Matrix (Zd d L) (Zd d L) ℂ) : Prop :=
  TransInv M ∧ ∀ x y, M (-x) (-y) = M x y

/-- The self-energy matrices below order `N` are invariant under translations and under
the reflection. -/
private lemma sigUpTo_SK (Sig : ℕ → Expansion 2) (S : Matrix (Zd d L) (Zd d L) ℝ)
    (hT : TransInv S) (hs : ∀ x y, S x y = S y x) (z : ℂ) : ∀ N k, SK (sigUpTo Sig S z N k) := by
  intro N
  induction N with
  | zero => intro k; exact ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
  | succ N ih =>
    intro k
    simp only [sigUpTo]
    by_cases hk : k = N
    · subst hk
      rw [Function.update_self]
      exact symKer_val S hT hs z _ ih (Sig k)
    · rw [Function.update_of_ne hk]
      exact ih k

/-- The self-energy matrices of a family are translation invariant when the variance matrix is
translation invariant and symmetric. -/
private lemma sigMat_transInv (Sig : ℕ → Expansion 2) (S : Matrix (Zd d L) (Zd d L) ℝ)
    (hT : TransInv S) (hs : ∀ x y, S x y = S y x) (z : ℂ) (l : ℕ) :
    TransInv (sigMat Sig S z l) :=
  (symKer_val S hT hs z _ (sigUpTo_SK Sig S hT hs z l) (Sig l)).1

/-- The chain `Θ Σ_{o₁} Θ ⋯ Σ_{o_l} Θ` is translation invariant when `Θ` and every `Σ_l` are. -/
private lemma chain_transInv (D : Data (Zd d L)) (hTh : TransInv D.Theta)
    (hSig : ∀ l, TransInv (D.Sig l)) (o : List ℕ) : TransInv (D.chain o) := by
  unfold Data.chain
  have key : ∀ (l : List ℕ) (A : Matrix (Zd d L) (Zd d L) ℂ), TransInv A →
      TransInv (l.foldl (fun M l => M * D.Sig l * D.Theta) A) := by
    intro l
    induction l with
    | nil => intro A hA; exact hA
    | cons a l ih =>
      intro A hA
      exact ih _ (TransInv_mul _ _ (TransInv_mul _ _ hA (hSig a)) hTh)
  exact key o _ hTh

/-- The factor of one component on the data record at the translated sample is the factor at the
translated atoms on the data record at the sample. -/
private lemma comp_val_Tm (hs : (Smat P.ψ W L).IsSymm) (a : Zd d L) (ω : Sample (Zd d L))
    {V : Type*} (σ : V → Zd d L) (c : Comp V) :
    Comp.val (rbmData d P Sig W L z (Tm (Equiv.addRight a) ω)) σ c =
      Comp.val (rbmData d P Sig W L z ω) (fun v => σ v + a) c := by
  have hT := Smat_transInv d L P.ψ W
  have hC := transInv_map_ofReal _ hT
  have hS1 : TransInv (rbmData d P Sig W L z ω).S := hC
  have hSp : TransInv (rbmData d P Sig W L z ω).Sp :=
    transInv_mul_inv_one_sub _ (transInv_smul_c _ hC)
  have hSm : TransInv (rbmData d P Sig W L z ω).Sm := fun x y a => by
    have := hSp x y a
    change star ((rbmData d P Sig W L z ω).Sp (x + a) (y + a)) =
      star ((rbmData d P Sig W L z ω).Sp x y)
    rw [this]
  have hTh : TransInv (rbmData d P Sig W L z ω).Theta :=
    transInv_mul_inv_one_sub _ (transInv_smul_c _ hC)
  have hSig : ∀ l, TransInv ((rbmData d P Sig W L z ω).Sig l) := fun l =>
    sigMat_transInv Sig _ hT (fun x y => hs.apply y x) z l
  have hCh : ∀ o, TransInv ((rbmData d P Sig W L z ω).chain o) := fun o =>
    chain_transInv _ hTh hSig o
  have hm : (rbmData d P Sig W L z (Tm (Equiv.addRight a) ω)).m =
      (rbmData d P Sig W L z ω).m := rfl
  rcases c with ⟨kind, x, y, minor, label⟩
  have hg := gm_Tm P Sig W z a ((minor.map σ).toFinset) ω
  have hU := toFinset_map_add a σ minor
  cases kind with
  | G ch => simp only [Comp.val, hU, hg]
  | weight ch => simp only [Comp.val, hU, hg]
  | light ch => simp only [Comp.val, hU, hg, hm]
  | inv ch => simp only [Comp.val, hU, hg]
  | wD ch D => simp only [Comp.val, hU, hg, hm]
  | waved w =>
    cases w
    · exact (hS1 _ _ a).symm
    · exact (hSp _ _ a).symm
    · exact (hSm _ _ a).symm
  | theta o => exact (hCh o _ _ a).symm
  | thetaErr n D => rfl
  | ghost => rfl
  | aux j r b => rfl
  | dot => simp only [Comp.val, add_left_inj]
  | xdot => simp only [Comp.val, add_left_inj]

/-! ### The values of the labelled graphs are covariant -/

/-- The variance matrix is invariant under the translation by `a`. -/
private lemma hSe_of (a : Zd d L) (x y : Zd d L) :
    Smat P.ψ W L ((Equiv.addRight a) x) ((Equiv.addRight a) y) = Smat P.ψ W L x y :=
  Smat_transInv d L P.ψ W x y a

/-- The term of a labelled graph on the data record at the translated sample is the term at the
translated atoms on the data record at the sample. -/
private lemma termR_Tm (hs : (Smat P.ψ W L).IsSymm) (a : Zd d L) (ω : Sample (Zd d L))
    {k n : ℕ} (Γ : Graph k n) (σ : Atom k n → Zd d L) :
    Γ.termR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) σ (Tm (Equiv.addRight a) ω) =
      Γ.termR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) (fun u => σ u + a) ω := by
  unfold Graph.termR
  have hm : (rbmData d P Sig W L z (Tm (Equiv.addRight a) ω)).m =
      (rbmData d P Sig W L z ω).m := rfl
  rw [hm]
  congr 2
  · exact congrArg (List.prod : List ℂ → ℂ)
      (List.map_congr_left fun c _ => comp_val_Tm P Sig W z hs a ω σ c)
  · refine List.map_congr_left fun ℓ _ => ?_
    obtain ⟨pq, u⟩ := ℓ
    have hf : ∀ ω', ((Γ.comps.filter fun c => decide (c.label = some (pq, u))).map
        (Comp.val (rbmData d P Sig W L z (Tm (Equiv.addRight a) ω')) σ)).prod =
        ((Γ.comps.filter fun c => decide (c.label = some (pq, u))).map
          (Comp.val (rbmData d P Sig W L z ω') (fun v => σ v + a))).prod := fun ω' =>
      congrArg (List.prod : List ℂ → ℂ)
        (List.map_congr_left fun c _ => comp_val_Tm P Sig W z hs a ω' σ c)
    have hP := Pexp_Tm (Smat P.ψ W L) (Equiv.addRight a) (hSe_of P W a) (fun x y => hs.apply y x)
      (σ u)
      (fun ω' => ((Γ.comps.filter fun c => decide (c.label = some (pq, u))).map
        (Comp.val (rbmData d P Sig W L z ω') σ)).prod)
      (fun ω' => ((Γ.comps.filter fun c => decide (c.label = some (pq, u))).map
        (Comp.val (rbmData d P Sig W L z ω') (fun v => σ v + a))).prod) hf ω
    cases pq
    · exact hP
    · simp only [PFamily.op, Pi.sub_apply]
      rw [hf ω]
      exact congrArg (fun t => _ - t) hP

/-- The value of a labelled graph on the data record at the translated sample is the value at the
translated external atoms on the data record at the sample. -/
private lemma valR_Tm (hs : (Smat P.ψ W L).IsSymm) (a : Zd d L) (ω : Sample (Zd d L))
    {k n : ℕ} (Γ : Graph k n) (e' : Fin k → Zd d L) :
    Γ.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) e' (Tm (Equiv.addRight a) ω) =
      Γ.valR ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) (fun i => e' i + a) ω := by
  unfold Graph.valR
  refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin n)) (Equiv.addRight a)) _ _
    fun s => ?_
  rw [termR_Tm P Sig W z hs a ω Γ]
  congr 1
  funext u
  cases u <;> rfl

/-- The sum of the rooted graphs of a formal sum on the data record at the translated sample is the
sum at the translated external atoms on the data record at the sample. -/
private lemma gammaVal_Tm (hs : (Smat P.ψ W L).IsSymm) (a : Zd d L) (E : Expansion 3)
    (x b : Zd d L) (ω : Sample (Zd d L)) :
    gammaVal E ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) x b (Tm (Equiv.addRight a) ω) =
      gammaVal E ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) (x + a) (b + a) ω := by
  unfold gammaVal
  refine congrArg (List.sum : List ℂ → ℂ) (List.map_congr_left fun g _ => ?_)
  rw [valR_Tm P Sig W z hs a ω]
  have h : (fun i => ![x, b, b] i + a) = ![x + a, b + a, b + a] := by
    funext i
    fin_cases i <;> rfl
  rw [h]

end Cov

/-! ## The four matrices are translation invariant -/

section Final

variable {d L : ℕ} [NeZero L] (P : Profile d) (W : ℕ) (z : ℂ)

/-- Integrals against the law of the model on `Z_L^d` are invariant under the action of a
translation. -/
private lemma integral_Tt (hs : (Smat P.ψ W L).IsSymm) (a : Zd d L) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Sample (Zd d L) → E) :
    ∫ ω, g (Tm (Equiv.addRight a) ω) ∂(gaussLaw (Smat P.ψ W L)) =
      ∫ ω, g ω ∂(gaussLaw (Smat P.ψ W L)) :=
  integral_Tm (Smat P.ψ W L) (Equiv.addRight a) (hSe_of P W a) (fun x y => hs.apply y x) g

/-- `E T_{xy}` as an integral against the Gaussian law. -/
private lemma expT_eq (x y : Zd d L) : expT d P W L z x y =
    ∫ ω, Tvar (Smat P.ψ W L) (green (hmat ω) z) (msc z) x y ∂(gaussLaw (Smat P.ψ W L)) := rfl

/-- `E |G_{xy}|²` as an integral against the Gaussian law. -/
private lemma expG2_eq (x y : Zd d L) : expG2 d P W L z x y =
    ∫ ω, ‖green (hmat ω) z x y‖ ^ 2 ∂(gaussLaw (Smat P.ψ W L)) := rfl

/-- `E[F]` as an integral against the Gaussian law. -/
private lemma expC_eq (F : Sample (Zd d L) → ℂ) :
    expC d P W L F = ∫ ω, F ω ∂(gaussLaw (Smat P.ψ W L)) := rfl

/-- `E T_{xy}` is translation invariant. -/
private lemma expT_inv (hs : (Smat P.ψ W L).IsSymm) (x y a : Zd d L) :
    expT d P W L z (x + a) (y + a) = expT d P W L z x y := by
  rw [expT_eq, expT_eq]
  rw [show (fun ω => Tvar (Smat P.ψ W L) (green (hmat ω) z) (msc z) (x + a) (y + a)) =
    fun ω => (fun ω' => Tvar (Smat P.ψ W L) (green (hmat ω') z) (msc z) x y)
      (Tm (Equiv.addRight a) ω) from funext fun ω => by
        simp only [Tvar, green_Tm]
        congr 1
        exact (Fintype.sum_equiv (Equiv.addRight a) _ _ fun α => by
          simp only [Equiv.coe_addRight]
          rw [Smat_transInv d L P.ψ W x α a]).symm]
  exact integral_Tt P W hs a (fun ω' => Tvar (Smat P.ψ W L) (green (hmat ω') z) (msc z) x y)

/-- `E |G_{xy}|²` is translation invariant. -/
private lemma expG2_inv (hs : (Smat P.ψ W L).IsSymm) (x y a : Zd d L) :
    expG2 d P W L z (x + a) (y + a) = expG2 d P W L z x y := by
  rw [expG2_eq, expG2_eq]
  rw [show (fun ω => ‖green (hmat ω) z (x + a) (y + a)‖ ^ 2) =
    fun ω => (fun ω' => ‖green (hmat ω') z x y‖ ^ 2) (Tm (Equiv.addRight a) ω) from
      funext fun ω => by simp only [green_Tm]]
  exact integral_Tt P W hs a (fun ω' => ‖green (hmat ω') z x y‖ ^ 2)

/-- The expectation of the diagonal term of the local correction is translation invariant. -/
private lemma expC_diag_inv (hs : (Smat P.ψ W L).IsSymm) (b a : Zd d L) :
    expC d P W L (fun ω => star (green (hmat ω) z (b + a) (b + a)) - star (msc z)) =
      expC d P W L (fun ω => star (green (hmat ω) z b b) - star (msc z)) := by
  rw [expC_eq, expC_eq]
  rw [show (fun ω => star (green (hmat ω) z (b + a) (b + a)) - star (msc z)) =
    fun ω => (fun ω' => star (green (hmat ω') z b b) - star (msc z)) (Tm (Equiv.addRight a) ω)
      from funext fun ω => by simp only [green_Tm]]
  exact integral_Tt P W hs a (fun ω' => star (green (hmat ω') z b b) - star (msc z))

/-- The expectation of the sum of the rooted graphs of a formal sum is translation invariant. -/
private lemma expC_gamma_inv (hs : (Smat P.ψ W L).IsSymm) (Sig : ℕ → Expansion 2)
    (E : Expansion 3) (x b a : Zd d L) :
    expC d P W L (gammaVal E ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) (x + a) (b + a)) =
      expC d P W L (gammaVal E ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) x b) := by
  rw [expC_eq, expC_eq]
  rw [show (gammaVal E ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) (x + a) (b + a)) =
    fun ω => (gammaVal E ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) x b)
      (Tm (Equiv.addRight a) ω) from funext fun ω => (gammaVal_Tm P Sig W z hs a E x b ω).symm]
  exact integral_Tt P W hs a (gammaVal E ⟨Pexp (Smat P.ψ W L)⟩ (rbmData d P Sig W L z) x b)

end Final

end ModelSymm

/-- **Translation invariance of the model** ([I, Assumption 1.1], used in [I, (1.35)–(1.36)]): at
every `(W, L)` where the variance matrix `S_{W,L}` is symmetric and every `z` with `Im z > 0`,
for every family of self-energies and every `T`-equation, the matrices `E T_{xy}`,
`E |G_{xy}|²`, the local correction `𝒢` of [I, (8.16)] and the error of [I, (8.15), (8.20)] are
translation invariant. -/
theorem modelTransInv : modelTransInvStmt := by
  intro d P Sig 𝒬 W L _ z hs _
  refine ⟨fun x y a => ?_, fun x y a => ?_, fun x b a => ?_, fun x b a => ?_⟩
  · simp only [Matrix.of_apply, ModelSymm.expT_inv P W z hs x y a]
  · simp only [Matrix.of_apply, ModelSymm.expG2_inv P W z hs x y a]
  · simp only [corrMat, Matrix.of_apply, add_left_inj,
      ModelSymm.expC_gamma_inv P W z hs Sig _ x b a]
    by_cases hxb : x = b
    · subst hxb
      simp only [ite_true, ModelSymm.expC_diag_inv P W z hs x a]
    · simp only [hxb, ite_false]
  · simp only [errMat, Matrix.of_apply, ModelSymm.expC_gamma_inv P W z hs Sig _ x b a]

namespace ModelSymm

end ModelSymm

end RBM8D
