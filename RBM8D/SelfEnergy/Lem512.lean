import RBM8D.LocalLaw.Primed
import RBM8D.LocalLaw.Bridge
import RBM8D.Graph.ValueLemmas
import Batteries.Tactic.OpenPrivate

/-!
# The bounds of [I, Lemma 5.12] on the graphs of `R` and on the graphs of `A` with internal atoms

[I, (5.41)–(5.42)] in the strong norm, at `𝔟₁ = 𝔟₂ = 𝔟` and summed over `𝔞, 𝔟`, read from the
bound of [II, Claim 8.6] with the diagonal scaling order `n_𝔟` per graph (`graphSum''`) and
`Σ_y B_{ay} ≤ C L²/W²` ([II, (8.33)]), under the local law `|G_{xy} − m δ_{xy}|² ≺ B_{xy}`
([I, Theorem 2.16] in the form of `localLawTExpStmt'`), which is `‖G − m‖_{s;(1,1)} ≺ 1`:

* `Lem512.graphRowsStmt`: for one graph of the kinds of [II, Def 3.2] with the properties read by
  [II, Claim 8.6], along any filter below the filter of the local law and at any spectral
  parameter in `𝐃(κ, ε)`, `Σ_{𝔞,𝔟} E|𝒢_{𝔞,𝔟𝔟}|` is at most `W^δ L^d (L²/W²) W^{−(n_𝔟−2)d/2}` for a
  `⊕`-recollision graph at `𝔟₁ = 𝔟₂` with `n_𝔟 ≥ 2`, and `W^δ L^d (L²/W²)² W^{−(n_𝔟−2)d/2}` for a
  graph with an internal atom that is not one and is rooted at the external atoms;
* `Lem512.recordRowsStmt`: for a record with the graph properties of [II, Def 3.2] and the
  clauses of [II, Def 6.3] at order `n`, the sum over `R` is at most `W^δ L^d (L²/W²) W^{−d/2}`
  ([I, (5.41)] summed over `3 ≤ k ≤ n`), and the sum over the graphs of `A` with an internal
  atom is at most `W^δ L^d ((L²/W²) W^{−(n−3)d/2} + (L²/W²)² W^{−(n−1)d/2})` ([I, (5.42)]).

The expectation is split on the event of the local law: off it, an a priori bound polynomial in
`W` and the probability `W^{−D}` of the exceptional event.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Filter

namespace RBM8D

open Graphs

open private Moment_apriori_graph Moment_ev_adm Moment_tendsto Moment_W_le_L Moment_bB_le_one
  Moment_ev_list Moment_diagRecoll_of_recoll Moment_diagRecoll_of_pmBlock
  from RBM8D.LocalLaw.Moment
open private LabelRemoval_val_rbm from RBM8D.LocalLaw.LabelRemoval

/-! ## The statements -/

/-- **[I, Lemma 5.12], (5.41)–(5.42) per graph**, in the strong norm: for `d ≥ 8`, a profile `P`,
`c₀, c₁ > 0` with `c₀ + c₁ < 1`, `κ, ε > 0`, `c₀ᵀ`, the self-energies `Σ_l` of the even orders
`4 ≤ l ≤ N`, the local law `|G_{xy}(z) − m(z) δ_{xy}|² ≺ B_{xy}` uniformly in `z ∈ 𝐃(κ, ε)` and
`x, y` along `llFilter d N c₀ c₁ c₀ᵀ`, a filter `F` below it, spectral parameters `z_p ∈ 𝐃(κ, ε)`
eventually along `F`, and a graph `𝒢` normal regular, of the kinds of [II, Def 3.2] with labels
in `[4, N]`, with one diffusive edge at each external atom ([II, Def 3.2 (9)]), doubly connected,
with only diffusive edges at `⊗`, dotted edges forming a forest and without `P`/`Q` labels: for
every `δ > 0`, eventually along `F`,
* if `𝒢` is a `⊕`-recollision graph at `𝔟₁ = 𝔟₂` with `n_𝔟 ≥ 2`,
  `Σ_{𝔞,𝔟} E|𝒢_{𝔞,𝔟𝔟}(z_p)| ≤ W^δ L^d (L²/W²) W^{−(n_𝔟−2)d/2}`;
* if `𝒢` has an internal atom, is not a `⊕`-recollision graph at `𝔟₁ = 𝔟₂` and is rooted at the
  external atoms, `Σ_{𝔞,𝔟} E|𝒢_{𝔞,𝔟𝔟}(z_p)| ≤ W^δ L^d (L²/W²)² W^{−(n_𝔟−2)d/2}`.

With `L²/W² = W^ε/η` at `η = W^{2+ε}/L²`, these give [I, (5.41)] with `k = n_𝔟`, and
[I, (5.42)] for `n_𝔟 ≥ n + 1`, up to `W^{O(ε)}`. -/
def Lem512.graphRowsStmt : Prop :=
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ (N : ℕ) (Sig : ℕ → Expansion 2), SelfEnergiesUpTo d (smatVar P) Sig N →
    StochDom (llFilter d N c₀ c₁ c₀T) sizeW (rbmLaw d P)
      (U := fun p => {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} × Zd d p.1.2 × Zd d p.1.2)
      (fun _ v ω => ‖entryErr (green (hmat ω) v.1.1) (msc v.1.1) v.2.1 v.2.2‖ ^ 2)
      (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2) →
    ∀ (F : Filter SizeL), F ≤ llFilter d N c₀ c₁ c₀T → ∀ z : SizeL → ℂ,
      (∀ᶠ p in F, z p ∈ specDom κ ε p.1.1 p.1.2) →
    ∀ (nI C : ℕ) (g : Graph 3 nI), g.Normal C → g.TKinds N → g.AtExternals →
      g.DoublyConnected → g.TensorDiffusive → g.DotsAcyclic → g.LabelFree →
    ∀ δ : ℝ, 0 < δ → ∀ᶠ p in F,
      (g.DiagRecoll → 2 ≤ g.diagOrd →
        ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2,
          ∫ ω, ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
            ![a, b, b] ω‖ ∂(rbmLaw d P p) ≤
          (p.1.1 : ℝ) ^ δ * (p.1.2 : ℝ) ^ d * ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) *
            (p.1.1 : ℝ) ^ (-(((g.diagOrd : ℝ) - 2) * d / 2))) ∧
      (nI ≠ 0 → ¬ g.DiagRecoll → g.RootedAtExt →
        ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2,
          ∫ ω, ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
            ![a, b, b] ω‖ ∂(rbmLaw d P p) ≤
          (p.1.1 : ℝ) ^ δ * (p.1.2 : ℝ) ^ d * ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) ^ 2 *
            (p.1.1 : ℝ) ^ (-(((g.diagOrd : ℝ) - 2) * d / 2)))

/-- **[I, Lemma 5.12], (5.41)–(5.42)** for a record with the graph properties of [II, Def 3.2]
(`TRec.Shape N n D`, labels in `[4, N]`) and the clauses of [II, Def 6.3] (`TRec.Def63`), at an
order `n ≥ 1`, in the strong norm: with the hypotheses of `Lem512.graphRowsStmt` on `d`, `P`, the
constants, `Σ`, the local law, `F` and `z`, for every `δ > 0`, eventually along `F`,
* `Σ_{𝒢 ∈ R} Σ_{𝔞,𝔟} E|𝒢_{𝔞,𝔟𝔟}(z_p)| ≤ W^δ L^d (L²/W²) W^{−d/2}`, the sum of [I, (5.41)] over
  `3 ≤ k ≤ n`;
* `Σ_{𝒢 ∈ A, n_𝒢 ≥ 1} Σ_{𝔞,𝔟} E|𝒢_{𝔞,𝔟𝔟}(z_p)| ≤
  W^δ L^d ((L²/W²) W^{−(n−3)d/2} + (L²/W²)² W^{−(n−1)d/2})`, [I, (5.42)] for the graphs of `A`
  with internal atoms: the first term for the `⊕`-recollision graphs at `𝔟₁ = 𝔟₂`, the second for
  the others.

For an `n`-th order `T`-equation `𝒬` the record is `𝒬.toTRec` with `N = n − 1`. -/
def Lem512.recordRowsStmt : Prop :=
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε c₀T : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ (N n D : ℕ) (Sig : ℕ → Expansion 2) (𝒯 : TRec), 1 ≤ n →
    SelfEnergiesUpTo d (smatVar P) Sig N → 𝒯.Shape N n D → 𝒯.Def63 →
    StochDom (llFilter d N c₀ c₁ c₀T) sizeW (rbmLaw d P)
      (U := fun p => {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} × Zd d p.1.2 × Zd d p.1.2)
      (fun _ v ω => ‖entryErr (green (hmat ω) v.1.1) (msc v.1.1) v.2.1 v.2.2‖ ^ 2)
      (fun p v _ => bB d p.1.2 p.1.1 v.2.1 v.2.2) →
    ∀ (F : Filter SizeL), F ≤ llFilter d N c₀ c₁ c₀T → ∀ z : SizeL → ℂ,
      (∀ᶠ p in F, z p ∈ specDom κ ε p.1.1 p.1.2) →
    ∀ δ : ℝ, 0 < δ → ∀ᶠ p in F,
      (𝒯.R.map fun g => ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2,
          ∫ ω, ‖g.2.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
            ![a, b, b] ω‖ ∂(rbmLaw d P p)).sum ≤
        (p.1.1 : ℝ) ^ δ * (p.1.2 : ℝ) ^ d * ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) *
          (p.1.1 : ℝ) ^ (-((d : ℝ) / 2)) ∧
      ((𝒯.A.filter fun g => g.1 ≠ 0).map fun g => ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2,
          ∫ ω, ‖g.2.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
            ![a, b, b] ω‖ ∂(rbmLaw d P p)).sum ≤
        (p.1.1 : ℝ) ^ δ * (p.1.2 : ℝ) ^ d *
          (((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) * (p.1.1 : ℝ) ^ (-(((n : ℝ) - 3) * d / 2)) +
            ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) ^ 2 * (p.1.1 : ℝ) ^ (-(((n : ℝ) - 1) * d / 2)))

/-! ## The weak norm of an entrywise bound `t B^{1/2}` -/

/-- An entrywise bound `|A_{xy}| ≤ t B_{xy}^{1/2}` gives `‖A‖_{s;(1,2)} ≤ t`, since
`(W/⟨x−y⟩)² ⟨x−y⟩^{d/2} B_{xy}^{1/2} = W/⟨x−y⟩ ≤ 1`. -/
private theorem Lem512_strongNorm_le (d L W : ℕ) [NeZero L] (hW : 1 ≤ W)
    (A : Matrix (Zd d L) (Zd d L) ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hA : ∀ x y, |A x y| ≤ t * Real.sqrt (bB d L W x y)) :
    0 ≤ strongNorm d L W 1 2 A ∧ strongNorm d L W 1 2 A ≤ t := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hbrk : ∀ x y : Zd d L, (W : ℝ) ≤ brk d L W x y := fun x y => by
    unfold brk; have := Nat.cast_nonneg (α := ℝ) (zdistInf d L (x - y)); linarith
  have h1 := (bB_strongNorm d L W hW).2
  unfold strongNorm at h1 ⊢
  constructor
  · have hb0 : 0 < brk d L W 0 0 := by linarith [hbrk 0 0]
    refine le_trans ?_ (le_ciSup (Finite.bddAbove_range _) (0 : Zd d L))
    refine le_trans ?_ (le_ciSup (Finite.bddAbove_range _) (0 : Zd d L))
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg hb0.le _)) (abs_nonneg _)
  · refine ciSup_le fun x => ciSup_le fun y => ?_
    have hb0 : 0 < brk d L W x y := by linarith [hbrk x y]
    have hq0 : 0 < (W : ℝ) / brk d L W x y := by positivity
    have hq1 : (W : ℝ) / brk d L W x y ≤ 1 := (div_le_one hb0).2 (hbrk x y)
    have hterm : ((W : ℝ) / brk d L W x y) ^ (1 : ℝ) * brk d L W x y ^ (1 * (d : ℝ) / 2) *
        |Real.sqrt (bB d L W x y)| ≤ 1 := by
      refine le_trans ?_ h1.le
      refine le_trans ?_ (le_ciSup (Finite.bddAbove_range _) x)
      exact le_ciSup (f := fun y => ((W : ℝ) / brk d L W x y) ^ (1 : ℝ) *
        brk d L W x y ^ (1 * (d : ℝ) / 2) * |Real.sqrt (bB d L W x y)|)
        (Finite.bddAbove_range _) y
    have hpow : ((W : ℝ) / brk d L W x y) ^ (2 : ℝ) ≤ ((W : ℝ) / brk d L W x y) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (by norm_num)
    have hA' : |A x y| ≤ t * |Real.sqrt (bB d L W x y)| := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact hA x y
    have hb1 : 0 ≤ brk d L W x y ^ (1 * (d : ℝ) / 2) := Real.rpow_nonneg hb0.le _
    calc ((W : ℝ) / brk d L W x y) ^ (2 : ℝ) * brk d L W x y ^ (1 * (d : ℝ) / 2) * |A x y|
        ≤ ((W : ℝ) / brk d L W x y) ^ (1 : ℝ) * brk d L W x y ^ (1 * (d : ℝ) / 2) *
            (t * |Real.sqrt (bB d L W x y)|) := by
          gcongr
      _ = t * (((W : ℝ) / brk d L W x y) ^ (1 : ℝ) * brk d L W x y ^ (1 * (d : ℝ) / 2) *
            |Real.sqrt (bB d L W x y)|) := by ring
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left hterm ht
      _ = t := mul_one t

/-- An entrywise bound `|A_{xy}| ≤ t B_{xy}^{1/2}` gives `‖A‖_{w;(1,2)} ≤ C t` with `C` depending
only on `d ≥ 4` ([I, (6.11)–(6.13)]: the weak norm is bounded by the strong norm). -/
private theorem Lem512_weakNorm_le (d : ℕ) (hd : 4 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (L W : ℕ) [NeZero L], 1 ≤ W → ∀ (A : Matrix (Zd d L) (Zd d L) ℝ) (t : ℝ), 0 ≤ t →
      (∀ x y, |A x y| ≤ t * Real.sqrt (bB d L W x y)) → weakNorm d L W 1 2 A ≤ C * t := by
  have hd' : (4 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C, hC⟩ := weak_le_strong d 1 2 (by linarith) (by linarith)
  refine ⟨|C|, abs_nonneg _, fun L W _ hW A t ht hA => ?_⟩
  obtain ⟨hs0, hs⟩ := Lem512_strongNorm_le d L W hW A t ht hA
  calc weakNorm d L W 1 2 A ≤ C * strongNorm d L W 1 2 A := hC L W hW A
    _ ≤ |C| * strongNorm d L W 1 2 A := mul_le_mul_of_nonneg_right (le_abs_self _) hs0
    _ ≤ |C| * t := mul_le_mul_of_nonneg_left hs (abs_nonneg _)

/-! ## Values on the data record of the model -/

/-- A graph with the kinds of [II, Def 3.2] has the same value on the data record of the model at
the sample `ω` and on the data record at the single matrix `G = G(ω)`. -/
private theorem Lem512_val_rbm {d : ℕ} (P : Profile d) (Sig : ℕ → Expansion 2) (W L : ℕ)
    [NeZero L] (z : ℂ) (ω : Sample (Zd d L)) {N nI : ℕ} (g : Graph 3 nI) (hK : g.TKinds N)
    (e : Fin 3 → Zd d L) :
    g.val (rbmData d P Sig W L z ω) e =
      g.val (gData (Smat P.ψ W L) z Sig (green (hmat ω) z)) e := by
  unfold Graph.val Graph.term
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 2
  refine List.map_congr_left fun c hc => ?_
  exact LabelRemoval_val_rbm P Sig W L z ω _ N c (Or.inl (List.all_eq_true.1 hK c hc))

/-! ## The expectation split on the exceptional event -/

/-- `E f ≤ A + M β` when `f ≤ A` off an event of probability at most `β` and `f ≤ M` everywhere,
with `A, M ≥ 0`. -/
private theorem Lem512_integral_le {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (bad : Set Ω) (A M β : ℝ) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hβ : 0 ≤ β) (hbad : μ bad ≤ ENNReal.ofReal β) (hgood : ∀ ω, ω ∉ bad → f ω ≤ A)
    (hall : ∀ ω, f ω ≤ M) : ∫ ω, f ω ∂μ ≤ A + M * β := by
  by_cases hf : Integrable f μ
  · set s := toMeasurable μ bad with hs
    have hsm : MeasurableSet s := measurableSet_toMeasurable μ bad
    have hint : Integrable (fun ω => A + s.indicator (fun _ => M) ω) μ :=
      (integrable_const A).add ((integrable_const M).indicator hsm)
    have hle : ∀ ω, f ω ≤ A + s.indicator (fun _ => M) ω := by
      intro ω
      by_cases hω : ω ∈ s
      · rw [Set.indicator_of_mem hω]; linarith [hall ω]
      · rw [Set.indicator_of_notMem hω, add_zero]
        exact hgood ω fun h => hω (subset_toMeasurable μ bad h)
    have hμs : μ.real s ≤ β := by
      rw [Measure.real, hs, measure_toMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal hβ hbad
    calc ∫ ω, f ω ∂μ ≤ ∫ ω, (A + s.indicator (fun _ => M) ω) ∂μ := integral_mono hf hint hle
      _ = A + μ.real s * M := by
          rw [integral_add (integrable_const A) ((integrable_const M).indicator hsm),
            integral_const, integral_indicator_const M hsm]
          simp [smul_eq_mul]
      _ ≤ A + M * β := by nlinarith
  · rw [integral_undef hf]
    have : 0 ≤ M * β := mul_nonneg hM hβ
    linarith

/-- The double sum over `𝔞, 𝔟` of the split of `Lem512_integral_le`, with the good bound
`c B_{𝔞𝔟}` and row sums of `B` at most `S`. -/
private theorem Lem512_sum_le {ι Ω : Type} [Fintype ι] [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : ι → ι → Ω → ℝ) (B : ι → ι → ℝ) (bad : Set Ω)
    (c M β S : ℝ) (hc : 0 ≤ c) (hB : ∀ a b, 0 ≤ B a b) (hM : 0 ≤ M) (hβ : 0 ≤ β)
    (hbad : μ bad ≤ ENNReal.ofReal β) (hS : ∀ a, ∑ b, B a b ≤ S)
    (hgood : ∀ a b ω, ω ∉ bad → f a b ω ≤ c * B a b) (hall : ∀ a b ω, f a b ω ≤ M) :
    ∑ a, ∑ b, ∫ ω, f a b ω ∂μ ≤
      (Fintype.card ι : ℝ) * (c * S) + (Fintype.card ι : ℝ) ^ 2 * (M * β) := by
  calc ∑ a, ∑ b, ∫ ω, f a b ω ∂μ ≤ ∑ a : ι, ∑ b : ι, (c * B a b + M * β) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          Lem512_integral_le μ (f a b) bad _ M β (mul_nonneg hc (hB a b)) hM hβ hbad
            (hgood a b) (hall a b)
    _ = ∑ a : ι, (c * ∑ b, B a b + (Fintype.card ι : ℝ) * (M * β)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
    _ ≤ ∑ a : ι, (c * S + (Fintype.card ι : ℝ) * (M * β)) :=
        Finset.sum_le_sum fun a _ => by gcongr; exact hS a
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The exponents at the end: with `2 C₁ ≤ W^{δ/2}`, `W ≥ 2`, `X ≥ 1` and `(W, L) ∈ adm(c₀, c₁)`,
`L^d · W^{δ/2} W^{−e} X · C₁ L²/W² + L^{2d} · W^K W^{−(|K| + 2d/c₁ + |e| + 1)}` is at most
`W^δ L^d (L²/W²) X W^{−e}`. -/
private theorem Lem512_arith {d : ℕ} {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (p : SizeL)
    (hp : p.1 ∈ adm c₀ c₁) (δ e K C₁ X : ℝ) (hX : 1 ≤ X) (hC₁ : 0 ≤ C₁)
    (hW2 : 2 ≤ (p.1.1 : ℝ)) (hWC : 2 * C₁ ≤ (p.1.1 : ℝ) ^ (δ / 2)) (hδ : 0 < δ) :
    (Fintype.card (Zd d p.1.2) : ℝ) * ((p.1.1 : ℝ) ^ (δ / 2) * (p.1.1 : ℝ) ^ (-e) * X *
        (C₁ * ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2))) +
      (Fintype.card (Zd d p.1.2) : ℝ) ^ 2 *
        ((p.1.1 : ℝ) ^ K * (p.1.1 : ℝ) ^ (-(|K| + 2 * d / c₁ + |e| + 1))) ≤
      (p.1.1 : ℝ) ^ δ * (p.1.2 : ℝ) ^ d * ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) * X *
        (p.1.1 : ℝ) ^ (-e) := by
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  set L : ℝ := (p.1.2 : ℝ) with hLdef
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  have hWL : W ≤ L := Moment_W_le_L hc₀ p hp
  have hL0 : 0 < L := by linarith
  have hcard : (Fintype.card (Zd d p.1.2) : ℝ) = L ^ d := by rw [card_Zd]; push_cast; rfl
  have hcardW : L ^ d ≤ W ^ ((d : ℝ) / c₁) := by
    have := card_Zd_le_adm d c₀ c₁ hc₁ p hp
    rw [hcard] at this; exact this
  have hR1 : 1 ≤ L ^ 2 / W ^ 2 := by
    rw [le_div_iff₀ (by positivity), one_mul]; exact pow_le_pow_left₀ hW0.le hWL 2
  have hLd1 : 1 ≤ L ^ d := one_le_pow₀ (by linarith)
  have hWd1 : 1 ≤ W ^ δ := Real.one_le_rpow hW1 hδ.le
  have hWe0 : 0 < W ^ (-e) := Real.rpow_pos_of_pos hW0 _
  have hhalf : W ^ (δ / 2) * W ^ (δ / 2) = W ^ δ := by rw [← Real.rpow_add hW0]; ring_nf
  have hWh0 : 0 ≤ W ^ (δ / 2) := Real.rpow_nonneg hW0.le _
  -- the first term
  have h1 : L ^ d * (W ^ (δ / 2) * W ^ (-e) * X * (C₁ * (L ^ 2 / W ^ 2))) ≤
      (1 / 2) * (W ^ δ * L ^ d * (L ^ 2 / W ^ 2) * X * W ^ (-e)) := by
    have hc : W ^ (δ / 2) * C₁ ≤ W ^ δ / 2 := by rw [← hhalf]; nlinarith
    have hpos : 0 ≤ L ^ d * W ^ (-e) * X * (L ^ 2 / W ^ 2) := by positivity
    calc L ^ d * (W ^ (δ / 2) * W ^ (-e) * X * (C₁ * (L ^ 2 / W ^ 2)))
        = (W ^ (δ / 2) * C₁) * (L ^ d * W ^ (-e) * X * (L ^ 2 / W ^ 2)) := by ring
      _ ≤ (W ^ δ / 2) * (L ^ d * W ^ (-e) * X * (L ^ 2 / W ^ 2)) :=
          mul_le_mul_of_nonneg_right hc hpos
      _ = _ := by ring
  -- the second term
  have h2 : (L ^ d) ^ 2 * (W ^ K * W ^ (-(|K| + 2 * d / c₁ + |e| + 1))) ≤ W ^ (-e) / 2 := by
    have hsq : (L ^ d) ^ 2 ≤ W ^ (2 * d / c₁) := by
      calc (L ^ d) ^ 2 ≤ (W ^ ((d : ℝ) / c₁)) ^ 2 := pow_le_pow_left₀ (by positivity) hcardW 2
        _ = W ^ (2 * d / c₁) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
    have hexp : W ^ (2 * d / c₁) * (W ^ K * W ^ (-(|K| + 2 * d / c₁ + |e| + 1))) ≤
        W ^ (-e) * W ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
      refine Real.rpow_le_rpow_of_exponent_le hW1 ?_
      have := le_abs_self K
      have := le_abs_self e
      linarith
    have hinv : W ^ (-1 : ℝ) ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hW2
    calc (L ^ d) ^ 2 * (W ^ K * W ^ (-(|K| + 2 * d / c₁ + |e| + 1)))
        ≤ W ^ (2 * d / c₁) * (W ^ K * W ^ (-(|K| + 2 * d / c₁ + |e| + 1))) :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
      _ ≤ W ^ (-e) * W ^ (-1 : ℝ) := hexp
      _ ≤ W ^ (-e) * (1 / 2) := mul_le_mul_of_nonneg_left hinv hWe0.le
      _ = W ^ (-e) / 2 := by ring
  have h3 : W ^ (-e) / 2 ≤ (1 / 2) * (W ^ δ * L ^ d * (L ^ 2 / W ^ 2) * X * W ^ (-e)) := by
    have : 1 ≤ W ^ δ * L ^ d * (L ^ 2 / W ^ 2) * X := by
      have h12 : 1 ≤ W ^ δ * L ^ d := one_le_mul_of_one_le_of_one_le hWd1 hLd1
      have h123 : 1 ≤ W ^ δ * L ^ d * (L ^ 2 / W ^ 2) := one_le_mul_of_one_le_of_one_le h12 hR1
      exact one_le_mul_of_one_le_of_one_le h123 hX
    nlinarith
  rw [hcard]
  linarith

/-! ## The bound per graph -/

/-- **[I, Lemma 5.12], (5.41)–(5.42) per graph** (`Lem512.graphRowsStmt`): off the exceptional
event of the local law the rows of `graphSum''` at `ε₀ = 0`, `Φ̃ = 0` (whose weak norm hypothesis
follows from the entrywise bound) and `Σ_y B_{ay} ≤ C L²/W²`; on it the a priori bound polynomial
in `W`. -/
theorem Lem512.graphRows : Lem512.graphRowsStmt := by
  intro d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε N Sig hSE hLL F hF z hz nI C g hN hK hAE hDC hTD
    hDA hLF δ hδ
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨τ', hτ', W₀, hW₀⟩ := graphSum'' d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε N Sig hSE nI C g hN
    hK hAE hDC hTD hDA 0 le_rfl (by positivity) (δ / 2) (by positivity)
  obtain ⟨C₁, hC₁0, hC₁⟩ := sumB1 d hd
  obtain ⟨Cw, hCw0, hCw⟩ := Lem512_weakNorm_le d (by omega)
  obtain ⟨K, hKev⟩ := Moment_apriori_graph d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε N Sig hSE
    (fun p => {w : ℂ // w ∈ specDom κ ε p.1.1 p.1.2}) (fun _ u => u.1) (fun _ u => u.2) g hK
  set e : ℝ := ((g.diagOrd : ℝ) - 2) * d / 2 with he
  set D' : ℝ := |K| + 2 * d / c₁ + |e| + 1 with hD'
  have hD'0 : 0 < D' := by
    have : 0 ≤ 2 * (d : ℝ) / c₁ := by positivity
    have := abs_nonneg K; have := abs_nonneg e; linarith
  have hsz : Tendsto sizeW F atTop := (Moment_tendsto d N c₀ c₁ c₀T).mono_left hF
  have hpow : ∀ r : ℝ, 0 < r → ∀ M : ℝ, ∀ᶠ p in F, M ≤ (p.1.1 : ℝ) ^ r := fun r hr M =>
    ((tendsto_rpow_atTop hr).comp hsz).eventually (eventually_ge_atTop M)
  filter_upwards [hz, (hLL τ' hτ' D' hD'0).filter_mono hF,
    (Moment_ev_adm d N c₀ c₁ c₀T).filter_mono hF, hKev.filter_mono hF,
    hsz.eventually (eventually_ge_atTop (max W₀ 2)), hpow (δ / 2) (by positivity) (2 * C₁),
    hpow (τ' / 2) (by positivity) (max Cw 1)] with p hzp hbad hadm hKp hW hWC hWw
  change max W₀ 2 ≤ (p.1.1 : ℝ) at hW
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  set L : ℝ := (p.1.2 : ℝ) with hLdef
  have hW2 : 2 ≤ W := (le_max_right _ _).trans hW
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  have hW1n : 1 ≤ p.1.1 := by
    have h : (1 : ℝ) ≤ (p.1.1 : ℝ) := hW1
    exact_mod_cast h
  have hWL : W ≤ L := Moment_W_le_L hc₀ p hadm
  have : IsProbabilityMeasure (rbmLaw d P p) := isProbabilityMeasure_gaussLaw _
  set bad := {ω | ∃ u : {z : ℂ // z ∈ specDom κ ε p.1.1 p.1.2} × Zd d p.1.2 × Zd d p.1.2,
    sizeW p ^ τ' * bB d p.1.2 p.1.1 u.2.1 u.2.2 <
      ‖entryErr (green (hmat ω) u.1.1) (msc u.1.1) u.2.1 u.2.2‖ ^ 2} with hbad_def
  -- off the exceptional event the hypotheses of `graphSum''` hold at `G = G(ω)`, `Φ̃ = 0`
  have hgood : ∀ ω, ω ∉ bad →
      (g.DiagRecoll → 2 ≤ g.diagOrd → ∀ a b : Zd d p.1.2,
        g.absVal (gData (Smat P.ψ p.1.1 p.1.2) (z p) Sig (green (hmat ω) (z p))) ![a, b, b] ≤
          (p.1.1 : ℝ) ^ (δ / 2) * (p.1.1 : ℝ) ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2) + 0)) *
            bB d p.1.2 p.1.1 a b) ∧
      (nI ≠ 0 → ¬ g.DiagRecoll → g.RootedAtExt → ∀ a b : Zd d p.1.2,
        g.absVal (gData (Smat P.ψ p.1.1 p.1.2) (z p) Sig (green (hmat ω) (z p))) ![a, b, b] ≤
          (p.1.1 : ℝ) ^ (δ / 2) * (p.1.1 : ℝ) ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2) + 0)) *
            ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) * (bB d p.1.2 p.1.1 a b + 0 ^ 2)) := by
    intro ω hω
    have hsq : ∀ x y, ‖entryErr (green (hmat ω) (z p)) (msc (z p)) x y‖ ^ 2 ≤
        W ^ τ' * bB d p.1.2 p.1.1 x y := by
      intro x y
      by_contra h
      exact hω ⟨(⟨z p, hzp⟩, x, y), lt_of_not_ge h⟩
    have hent : ∀ x y, ‖entryErr (green (hmat ω) (z p)) (msc (z p)) x y‖ ≤
        W ^ (τ' / 2) * Real.sqrt (bB d p.1.2 p.1.1 x y) := by
      intro x y
      have h := Real.sqrt_le_sqrt (hsq x y)
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (Real.rpow_nonneg hW0.le _),
        Real.sqrt_eq_rpow, ← Real.rpow_mul hW0.le] at h
      convert h using 3; ring
    have hτle : W ^ (τ' / 2) ≤ W ^ τ' :=
      Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    have hwn : weakNorm d p.1.2 p.1.1 1 2 (errAbs (green (hmat ω) (z p)) (z p)) ≤
        W ^ (0 + τ') := by
      refine (hCw p.1.2 p.1.1 hW1n _ (W ^ (τ' / 2)) (Real.rpow_nonneg hW0.le _)
        fun x y => ?_).trans ?_
      · simp only [errAbs, abs_norm]; exact hent x y
      · rw [zero_add]
        have hsplit : W ^ τ' = W ^ (τ' / 2) * W ^ (τ' / 2) := by
          rw [← Real.rpow_add hW0]; ring_nf
        rw [hsplit]
        exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans hWw)
          (Real.rpow_nonneg hW0.le _)
    have hent' : ∀ x y, ‖entryErr (green (hmat ω) (z p)) (msc (z p)) x y‖ ≤
        W ^ τ' * (Real.sqrt (bB d p.1.2 p.1.1 x y) + 0) := by
      intro x y
      rw [add_zero]
      exact (hent x y).trans (mul_le_mul_of_nonneg_right hτle (Real.sqrt_nonneg _))
    obtain ⟨r1, -, r3⟩ := hW₀ p.1.1 p.1.2 hadm ((le_max_left _ _).trans hW) (z p) hzp
      (green (hmat ω) (z p)) 0 le_rfl hwn hent'
    exact ⟨r1, r3⟩
  -- the value on the data record of the model is bounded by the absolute-value graph
  have hval : ∀ (a b : Zd d p.1.2) (ω : Sample (Zd d p.1.2)),
      ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p)) ![a, b, b] ω‖ ≤
        g.absVal (gData (Smat P.ψ p.1.1 p.1.2) (z p) Sig (green (hmat ω) (z p))) ![a, b, b] := by
    intro a b ω
    rw [Graph.valR_of_labelFree 3 nI g _ _ _ _ _ hLF]
    dsimp only
    rw [Lem512_val_rbm P Sig _ _ _ ω g hK]
    exact norm_val_le_absVal 3 nI _ g _ _
  have hall : ∀ (a b : Zd d p.1.2) (ω : Sample (Zd d p.1.2)),
      ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p)) ![a, b, b] ω‖ ≤
        W ^ K := fun a b ω => hKp ⟨z p, hzp⟩ a b ω
  have hβ : (0 : ℝ) ≤ W ^ (-D') := Real.rpow_nonneg hW0.le _
  have hB0 : ∀ a b : Zd d p.1.2, 0 ≤ bB d p.1.2 p.1.1 a b :=
    fun a b => (Moment_bB_le_one d p.1.2 p.1.1 (by omega) hW1 a b).1
  have hS : ∀ a : Zd d p.1.2, ∑ b, bB d p.1.2 p.1.1 a b ≤ C₁ * (L ^ 2 / W ^ 2) :=
    hC₁ p.1.2 p.1.1 hW1n
  have hexp : W ^ (((g.diagOrd : ℝ) - 2) * (-((d : ℝ) / 2) + 0)) = W ^ (-e) := by
    rw [he]; congr 1; ring
  have hR1 : 1 ≤ L ^ 2 / W ^ 2 := by
    rw [le_div_iff₀ (by positivity), one_mul]; exact pow_le_pow_left₀ hW0.le hWL 2
  have hbadμ : rbmLaw d P p bad ≤ ENNReal.ofReal (W ^ (-D')) := hbad
  constructor
  · intro hDR h2
    have hsum := Lem512_sum_le (rbmLaw d P p)
      (fun a b ω => ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
        ![a, b, b] ω‖) (bB d p.1.2 p.1.1) bad (W ^ (δ / 2) * W ^ (-e) * 1) (W ^ K) (W ^ (-D'))
      (C₁ * (L ^ 2 / W ^ 2)) (by positivity) hB0 (Real.rpow_nonneg hW0.le _) hβ hbadμ hS
      (fun a b ω hω => by
        refine (hval a b ω).trans ?_
        have := (hgood ω hω).1 hDR h2 a b
        rw [hexp] at this
        linarith)
      hall
    refine hsum.trans ?_
    have := Lem512_arith (d := d) hc₀ hc₁ p hadm δ e K C₁ 1 le_rfl hC₁0 hW2 hWC hδ
    rw [mul_one] at this ⊢
    rw [mul_one] at this
    exact this
  · intro hnI hDR hR
    have hsum := Lem512_sum_le (rbmLaw d P p)
      (fun a b ω => ‖g.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
        ![a, b, b] ω‖) (bB d p.1.2 p.1.1) bad (W ^ (δ / 2) * W ^ (-e) * (L ^ 2 / W ^ 2)) (W ^ K)
      (W ^ (-D')) (C₁ * (L ^ 2 / W ^ 2)) (by positivity) hB0 (Real.rpow_nonneg hW0.le _) hβ hbadμ
      hS
      (fun a b ω hω => by
        refine (hval a b ω).trans ?_
        have := (hgood ω hω).2 hnI hDR hR a b
        rw [hexp] at this
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at this
        linarith)
      hall
    refine hsum.trans ?_
    have := Lem512_arith (d := d) hc₀ hc₁ p hadm δ e K C₁ (L ^ 2 / W ^ 2) hR1 hC₁0 hW2 hWC hδ
    calc _ ≤ _ := this
      _ = _ := by ring

/-! ## The bound per record -/

/-- A sum of a list of terms, each at most `W^{δ/2} T`, with `length ≤ W^{δ/2}`, is at most
`W^δ T`. -/
private theorem Lem512_list_le {α : Type} (l : List α) (f : α → ℝ) (W δ T : ℝ) (hW : 0 < W)
    (hT : 0 ≤ T) (hl : (l.length : ℝ) ≤ W ^ (δ / 2)) (h : ∀ x ∈ l, f x ≤ W ^ (δ / 2) * T) :
    (l.map f).sum ≤ W ^ δ * T := by
  have hs := List.sum_le_length_nsmul (l.map f) (W ^ (δ / 2) * T) (by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact h y hy)
  rw [List.length_map, nsmul_eq_mul] at hs
  refine hs.trans ?_
  have hhalf : W ^ δ = W ^ (δ / 2) * W ^ (δ / 2) := by rw [← Real.rpow_add hW]; ring_nf
  rw [hhalf, mul_assoc]
  exact mul_le_mul_of_nonneg_right hl (mul_nonneg (Real.rpow_nonneg hW.le _) hT)

/-- `W^{−a} ≤ W^{−b}` for `b ≤ a` and `W ≥ 1`. -/
private theorem Lem512_rpow_neg_le (W a b : ℝ) (hW : 1 ≤ W) (h : b ≤ a) : W ^ (-a) ≤ W ^ (-b) :=
  Real.rpow_le_rpow_of_exponent_le hW (by linarith)

/-- **[I, Lemma 5.12], (5.41)–(5.42)** for a record (`Lem512.recordRowsStmt`): `Lem512.graphRows`
on each graph, with `n_𝔟 ≥ 3` on `R` (`⊕`, `⊖` in one dotted block force scaling order `≥ 5`),
`n_𝔟 ≥ n − 1` on the `⊕`-recollision graphs of `A` at `𝔟₁ = 𝔟₂`, and `n_𝔟 ≥ n + 1` on the other
graphs of `A` with an internal atom (by the clause on the external atoms `⊕`, `⊖` are not in one
dotted block); the number of graphs is absorbed in `W^{δ/2}`. -/
theorem Lem512.recordRows : Lem512.recordRowsStmt := by
  intro d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε N n D Sig 𝒯 hn hSE hSh h63 hLL F hF z hz δ hδ
  obtain ⟨⟨hS1, -⟩, hSR, hSA, -, -⟩ := hSh
  have h63' := TRec.def63G11_of_def63 𝒯 h63
  obtain ⟨⟨-, hA63, -⟩, -, -, hPM, -, -, hRoot, -, -⟩ := h63
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsz : Tendsto sizeW F atTop := (Moment_tendsto d N c₀ c₁ c₀T).mono_left hF
  have hrow : ∀ g ∈ 𝒯.R ++ 𝒯.A, ∀ᶠ p in F,
      (g.2.DiagRecoll → 2 ≤ g.2.diagOrd →
        ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2,
          ∫ ω, ‖g.2.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
            ![a, b, b] ω‖ ∂(rbmLaw d P p) ≤
          (p.1.1 : ℝ) ^ (δ / 2) * (p.1.2 : ℝ) ^ d * ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) *
            (p.1.1 : ℝ) ^ (-(((g.2.diagOrd : ℝ) - 2) * d / 2))) ∧
      (g.1 ≠ 0 → ¬ g.2.DiagRecoll → g.2.RootedAtExt →
        ∑ a : Zd d p.1.2, ∑ b : Zd d p.1.2,
          ∫ ω, ‖g.2.valR ⟨Pexp (Smat P.ψ p.1.1 p.1.2)⟩ (rbmData d P Sig p.1.1 p.1.2 (z p))
            ![a, b, b] ω‖ ∂(rbmLaw d P p) ≤
          (p.1.1 : ℝ) ^ (δ / 2) * (p.1.2 : ℝ) ^ d * ((p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2) ^ 2 *
            (p.1.1 : ℝ) ^ (-(((g.2.diagOrd : ℝ) - 2) * d / 2))) := by
    intro g hg
    have hg3 : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q := by
      simp only [List.mem_append] at hg ⊢; tauto
    have hg4 : g ∈ 𝒯.R ++ 𝒯.A ++ 𝒯.Q ++ 𝒯.Err := by
      simp only [List.mem_append] at hg ⊢; tauto
    obtain ⟨⟨C, hN⟩, hK, hAE, hDC⟩ := hS1 g hg3
    obtain ⟨hTD, hDA⟩ := h63'.1 g hg4
    have hLF : g.2.LabelFree := by
      rcases List.mem_append.1 hg with h | h
      · exact (hSR g h).1
      · exact (hSA g h).1
    exact Lem512.graphRows d hd P c₀ c₁ κ ε c₀T hc₀ hc₁ hc hκ hε N Sig hSE hLL F hF z hz g.1 C
      g.2 hN hK hAE hDC hTD hDA hLF (δ / 2) (by positivity)
  have hev := Moment_ev_list (𝒯.R ++ 𝒯.A) hrow
  filter_upwards [hev, (Moment_ev_adm d N c₀ c₁ c₀T).filter_mono hF,
    hsz.eventually (eventually_ge_atTop 1),
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < δ / 2)).comp hsz).eventually
      (eventually_ge_atTop ((𝒯.R ++ 𝒯.A).length : ℝ))] with p hp hadm hW hWl
  change (1 : ℝ) ≤ p.1.1 at hW
  change ((𝒯.R ++ 𝒯.A).length : ℝ) ≤ (p.1.1 : ℝ) ^ (δ / 2) at hWl
  set W : ℝ := (p.1.1 : ℝ) with hWdef
  set L : ℝ := (p.1.2 : ℝ) with hLdef
  have hW0 : 0 < W := by linarith
  have hWL : W ≤ L := Moment_W_le_L hc₀ p hadm
  have hR0 : 0 ≤ L ^ 2 / W ^ 2 := by positivity
  have hLd : 0 ≤ L ^ d := by positivity
  constructor
  · -- the graphs of `R`
    have hlen : ((𝒯.R).length : ℝ) ≤ W ^ (δ / 2) := by
      refine le_trans ?_ hWl
      rw [List.length_append]; push_cast
      have := Nat.cast_nonneg (α := ℝ) 𝒯.A.length; linarith
    have hT : 0 ≤ L ^ d * (L ^ 2 / W ^ 2) * W ^ (-((d : ℝ) / 2)) := by positivity
    have := Lem512_list_le 𝒯.R _ W δ _ hW0 hT hlen fun g hg => by
      have hgRA : g ∈ 𝒯.R ++ 𝒯.A := List.mem_append_left _ hg
      obtain ⟨hLF, hrec, h3, -⟩ := hSR g hg
      have hDR := Moment_diagRecoll_of_recoll g.2 hrec
      have hk : (3 : ℤ) ≤ g.2.diagOrd := by
        unfold Graph.diagOrd
        by_cases hpm : g.2.pmBlockB = true
        · have := hPM g hgRA hpm
          simp only [hpm, ite_true]; omega
        · simp only [Bool.not_eq_true] at hpm
          simp only [hpm]; simp; omega
      have hk' : (3 : ℝ) ≤ (g.2.diagOrd : ℝ) := by exact_mod_cast hk
      refine ((hp g hgRA).1 hDR (by omega)).trans ?_
      have hle := Lem512_rpow_neg_le W (((g.2.diagOrd : ℝ) - 2) * d / 2) ((d : ℝ) / 2) hW
        (by nlinarith)
      calc W ^ (δ / 2) * L ^ d * (L ^ 2 / W ^ 2) * W ^ (-(((g.2.diagOrd : ℝ) - 2) * d / 2))
          ≤ W ^ (δ / 2) * L ^ d * (L ^ 2 / W ^ 2) * W ^ (-((d : ℝ) / 2)) := by gcongr
        _ = W ^ (δ / 2) * (L ^ d * (L ^ 2 / W ^ 2) * W ^ (-((d : ℝ) / 2))) := by ring
    calc _ ≤ W ^ δ * (L ^ d * (L ^ 2 / W ^ 2) * W ^ (-((d : ℝ) / 2))) := this
      _ = _ := by ring
  · -- the graphs of `A` with an internal atom
    have hlen : (((𝒯.A.filter fun g => g.1 ≠ 0)).length : ℝ) ≤ W ^ (δ / 2) := by
      refine le_trans ?_ hWl
      rw [List.length_append]; push_cast
      have h1 : ((𝒯.A.filter fun g => g.1 ≠ 0).length : ℝ) ≤ 𝒯.A.length := by
        exact_mod_cast List.length_filter_le _ _
      have := Nat.cast_nonneg (α := ℝ) 𝒯.R.length; linarith
    set T : ℝ := L ^ d * ((L ^ 2 / W ^ 2) * W ^ (-(((n : ℝ) - 3) * d / 2)) +
      (L ^ 2 / W ^ 2) ^ 2 * W ^ (-(((n : ℝ) - 1) * d / 2))) with hTdef
    have hT1 : 0 ≤ (L ^ 2 / W ^ 2) * W ^ (-(((n : ℝ) - 3) * d / 2)) := by positivity
    have hT2 : 0 ≤ (L ^ 2 / W ^ 2) ^ 2 * W ^ (-(((n : ℝ) - 1) * d / 2)) := by positivity
    have hT : 0 ≤ T := by positivity
    have := Lem512_list_le (𝒯.A.filter fun g => g.1 ≠ 0) _ W δ T hW0 hT hlen fun g hg => by
      obtain ⟨hgA, hg0⟩ := List.mem_filter.1 hg
      have hg0' : g.1 ≠ 0 := by simpa using hg0
      have hgRA : g ∈ 𝒯.R ++ 𝒯.A := List.mem_append_right _ hgA
      obtain ⟨-, hord⟩ := hSA g hgA
      have hord' : (n : ℤ) + 1 ≤ g.2.ord := hord
      have hdo : g.2.ord - 2 ≤ g.2.diagOrd := by
        unfold Graph.diagOrd; split_ifs <;> omega
      by_cases hDR : g.2.DiagRecoll
      · have hk : (2 : ℤ) ≤ g.2.diagOrd := by
          unfold Graph.diagOrd
          by_cases hpm : g.2.pmBlockB = true
          · have := hPM g hgRA hpm
            simp only [hpm, ite_true]; omega
          · simp only [Bool.not_eq_true] at hpm
            simp only [hpm]; simp; omega
        have hk' : ((n : ℝ) - 1) ≤ (g.2.diagOrd : ℝ) := by
          have : ((n : ℤ) - 1) ≤ g.2.diagOrd := by omega
          exact_mod_cast this
        refine ((hp g hgRA).1 hDR hk).trans ?_
        have hle := Lem512_rpow_neg_le W (((g.2.diagOrd : ℝ) - 2) * d / 2)
          (((n : ℝ) - 3) * d / 2) hW (by nlinarith)
        calc W ^ (δ / 2) * L ^ d * (L ^ 2 / W ^ 2) * W ^ (-(((g.2.diagOrd : ℝ) - 2) * d / 2))
            ≤ W ^ (δ / 2) * L ^ d * (L ^ 2 / W ^ 2) * W ^ (-(((n : ℝ) - 3) * d / 2)) := by
              gcongr
          _ ≤ W ^ (δ / 2) * T := by
              rw [hTdef]
              have : 0 ≤ W ^ (δ / 2) * L ^ d := by positivity
              nlinarith
      · have hR := hRoot g (by simp only [List.mem_append]; tauto) hg0' hDR
        have hpm : g.2.pmBlockB = false := by
          by_contra hpm
          simp only [Bool.not_eq_false] at hpm
          rcases (hA63 g hgA).2 with ⟨h0, -⟩ | ⟨hE, -⟩
          · exact hg0' h0
          · exact hDR (Moment_diagRecoll_of_pmBlock g.2 hE hpm)
        have hk : (n : ℤ) + 1 ≤ g.2.diagOrd := by
          unfold Graph.diagOrd; simp only [hpm]; simp; omega
        have hk' : (n : ℝ) + 1 ≤ (g.2.diagOrd : ℝ) := by exact_mod_cast hk
        refine ((hp g hgRA).2 hg0' hDR hR).trans ?_
        have hle := Lem512_rpow_neg_le W (((g.2.diagOrd : ℝ) - 2) * d / 2)
          (((n : ℝ) - 1) * d / 2) hW (by nlinarith)
        calc W ^ (δ / 2) * L ^ d * (L ^ 2 / W ^ 2) ^ 2 *
              W ^ (-(((g.2.diagOrd : ℝ) - 2) * d / 2))
            ≤ W ^ (δ / 2) * L ^ d * (L ^ 2 / W ^ 2) ^ 2 * W ^ (-(((n : ℝ) - 1) * d / 2)) := by
              gcongr
          _ ≤ W ^ (δ / 2) * T := by
              rw [hTdef]
              have : 0 ≤ W ^ (δ / 2) * L ^ d := by positivity
              nlinarith
    calc _ ≤ W ^ δ * T := this
      _ = _ := by rw [hTdef]; ring

end RBM8D
