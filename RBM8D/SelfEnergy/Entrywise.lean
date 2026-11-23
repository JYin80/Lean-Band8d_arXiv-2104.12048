module

public import RBM8D.SelfEnergy.ContractShape
public import RBM8D.SelfEnergy.Diag

@[expose] public section

/-!
# The entrywise bound for `Σ_n`

For `d ≥ 8`, lower orders that are self-energies and `Σ_n` of the shape of an `n`-th order
self-energy, `G13.entrywise : G13.entrywiseStmt` is the first conjunct of `SelfEnergyBound` for
`Σ_n`: `|Σ_n(0, x)| ≤ L^τ W^{-(n-4)d/2} B_{0x}² + L^τ W^{-(n-2)d/2} 1_{x=0}` ([I, (1.26)] with the
diagonal term for the graphs of [I, Def 2.13 (i)]).

* `Entrywise.graph_bound`: one graph of the shape. `G13.dotContract` turns it into a graph with
  the same value that is normal regular with `x`, `y` internal, bounded by `detBound`
  ([I, Cor 6.12]), or diagonal, bounded by `G13.diagBound`; its value is bounded by its
  absolute-value graph, which reads the self-energy matrices only through its labels, so that the
  recursively computed matrices may be replaced by `Σ_l` (`sigUpTo_eq_sigMat`) and `smatVar P` by
  `S_{W,L}` (`smatVar_eq_on_adm`).
* `Entrywise.list_bound`: the sum over a formal sum, with one common `W₀`.
* The loss `L^τ` absorbs `W^{τ/2}` (`W ≤ L`) and the number of graphs (`L ≥ L₀`).
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-- **[I, (1.26)]** with the diagonal term, for `Σ_n`: for `d ≥ 8`, lower orders that are
self-energies and `Σ_n` of the shape of an `n`-th order self-energy,
`|Σ_n(0, x)| ≤ L^τ W^{-(n-4)d/2} B_{0x}² + L^τ W^{-(n-2)d/2} 1_{x=0}` with the quantifiers of
`SelfEnergyBound` ([I, Cor 6.12] for the graphs without dotted edge, the diagonal bound for the
graphs with one dotted edge between `x` and `y`). -/
def G13.entrywiseStmt : Prop :=
  ∀ (d : ℕ), 8 ≤ d → ∀ (P : Profile d) (n : ℕ) (Sig : ℕ → Expansion 2), 4 ≤ n →
    SelfEnergiesUpTo d (smatVar P) Sig (n - 1) → SelfEnergyShape n (Sig n) →
    ∀ κ ε c₀ c₁ : ℝ, 0 < κ → 0 < ε → 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
      ∀ τ : ℝ, 0 < τ → ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
        ∀ z ∈ specDom κ ε W L, ∀ x : Zd d L,
          ‖sigMat Sig (smatVar P W L) z n 0 x‖ ≤
            (L : ℝ) ^ τ * (W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
              (if x = 0 then (L : ℝ) ^ τ * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) else 0)

namespace Entrywise

/-- A component reads the self-energy matrices only through the entries of its label. -/
private theorem comp_val_sig {ι V : Type} [Fintype ι] [DecidableEq ι] (D : Data ι)
    (M : ℕ → Matrix ι ι ℂ) (σ : V → ι) (c : Comp V)
    (hc : ∀ o, c.kind = .theta o → ∀ l ∈ o, M l = D.Sig l) :
    Comp.val { D with Sig := M } σ c = Comp.val D σ c := by
  rcases c with ⟨kind, x, y, minor, label⟩
  cases kind with
  | theta o =>
    change (o.foldl (fun A l => A * M l * D.Theta) D.Theta) (σ x) (σ y) =
      (o.foldl (fun A l => A * D.Sig l * D.Theta) D.Theta) (σ x) (σ y)
    rw [List.foldl_ext _ _ _ fun a b hb => by rw [hc o rfl b hb]]
  | waved w => cases w <;> rfl
  | _ => rfl

/-- The absolute-value graph reads the self-energy matrices only through the entries of the
labels of its components. -/
private theorem absVal_sig {ι : Type} [Fintype ι] [DecidableEq ι] {k n : ℕ} (Γ : Graph k n)
    (D : Data ι) (M : ℕ → Matrix ι ι ℂ) (e : Fin k → ι)
    (hΓ : ∀ c ∈ Γ.comps, ∀ o, c.kind = .theta o → ∀ l ∈ o, M l = D.Sig l) :
    Γ.absVal { D with Sig := M } e = Γ.absVal D e := by
  unfold Graph.absVal
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  congr 1
  exact List.map_congr_left fun c hc => by rw [comp_val_sig D M _ c (hΓ c hc)]

/-- The absolute-value graph of a graph of deterministic kinds with labels in `[4, n - 1]` on the
record with the recursively computed matrices of orders `< n` is that on the record with `Σ_l`. -/
private theorem absVal_sigUpTo {ι : Type} [Fintype ι] [DecidableEq ι] {k m : ℕ} (Γ : Graph k m)
    (S : Matrix ι ι ℝ) (z : ℂ) (Sig : ℕ → Expansion 2) (n : ℕ)
    (hK : Γ.comps.all (Comp.isDetKind (n - 1)) = true) (e : Fin k → ι) :
    Γ.absVal (detData S z (sigUpTo Sig S z n)) e = Γ.absVal (detData S z (sigMat Sig S z)) e := by
  have := absVal_sig Γ (detData S z (sigMat Sig S z)) (sigUpTo Sig S z n) e (by
    intro c hc o ho l hl
    have h := List.all_eq_true.1 hK c hc
    simp only [Comp.isDetKind, ho, labelOK, Bool.and_eq_true, List.all_eq_true] at h
    have hl' : decide (4 ≤ l) = true ∧ decide (l ≤ n - 1) = true := ⟨(h.2 l hl).1.1, (h.2 l hl).1.2⟩
    simp only [decide_eq_true_eq] at hl'
    exact sigUpTo_eq_sigMat ι Sig S z l n (by omega))
  exact this

/-- The bound for the entry `(0, x)` of one graph of the shape of an `n`-th order self-energy,
with the recursively computed self-energy matrices, for `W` large along `adm(c₀, c₁)`. -/
theorem graph_bound :
    ∀ (d : ℕ), 6 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ (n : ℕ) (Sig : ℕ → Expansion 2),
      SelfEnergiesUpTo d (smatVar P) Sig (n - 1) →
      ∀ (m : ℕ) (Γ : Graph 2 m), SelfEnergyShape n [⟨m, Γ⟩] →
        ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ,
          ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
            ∀ x : Zd d L,
              ‖Γ.val (detData (smatVar P W L) z (sigUpTo Sig (smatVar P W L) z n)) ![0, x]‖ ≤
                (W : ℝ) ^ τ * ((W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
                  (if x = 0 then (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) else 0)) := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε n Sig hSig m Γ hsh τ hτ
  obtain ⟨W₁, hW₁⟩ := smatVar_eq_on_adm d P c₀ c₁ hc₀ hc₁
  obtain ⟨m', Γ', hsh', hval, hcase⟩ := G13.dotContract n m Γ hsh
  obtain ⟨-, hK, hO, hDC⟩ := hsh' _ (List.mem_singleton_self _)
  have hK : Γ'.comps.all (Comp.isDetKind (n - 1)) = true := hK
  have hO : Γ'.ord = (n : ℤ) := hO
  have hDC : Γ'.internalize.DoublyConnected := hDC
  have hnn : ∀ (W L : ℕ) [NeZero L] (x : Zd d L), 0 ≤
      (W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 := fun W L _ x => by positivity
  have hite : ∀ (W : ℕ), 0 ≤ (W : ℝ) ^ τ := fun W => by positivity
  rcases hcase with ⟨C, hN⟩ | hD
  · obtain ⟨W₂, hW₂⟩ := detBound d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε (n - 1) Sig hSig m' C Γ' hN hDC
      hK τ hτ
    refine ⟨max W₁ W₂, fun W L _ hm hW z hz x => ?_⟩
    have hW1 : W₁ ≤ W := (le_max_left _ _).trans hW
    have hW2 : W₂ ≤ W := (le_max_right _ _).trans hW
    rw [hW₁ W L hm hW1]
    have hb := hW₂ W L hm hW2 z hz 0 x
    rw [hO] at hb
    have hnz : 0 ≤ (if x = 0 then (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) else 0) := by
      split_ifs <;> positivity
    calc ‖Γ.val (detData (Smat P.ψ W L) z (sigUpTo Sig (Smat P.ψ W L) z n)) ![0, x]‖
        = ‖Γ'.val (detData (Smat P.ψ W L) z (sigUpTo Sig (Smat P.ψ W L) z n)) ![0, x]‖ := by
          rw [hval]
      _ ≤ Γ'.absVal (detData (Smat P.ψ W L) z (sigUpTo Sig (Smat P.ψ W L) z n)) ![0, x] :=
          norm_val_le_absVal _ _ _ _ _ _
      _ = Γ'.absVal (detData (Smat P.ψ W L) z (sigMat Sig (Smat P.ψ W L) z)) ![0, x] :=
          absVal_sigUpTo Γ' _ _ _ n hK _
      _ ≤ _ := hb
      _ ≤ _ := by
          push_cast
          have := hnn W L x
          nlinarith [hite W, mul_nonneg (hite W) hnz, mul_nonneg (hite W) this]
  · obtain ⟨W₂, hW₂⟩ := G13.diagBound d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε n Sig hSig m' Γ' hsh' hD τ
      hτ
    refine ⟨max W₁ W₂, fun W L _ hm hW z hz x => ?_⟩
    have hW1 : W₁ ≤ W := (le_max_left _ _).trans hW
    have hW2 : W₂ ≤ W := (le_max_right _ _).trans hW
    rw [hW₁ W L hm hW1]
    have hb := hW₂ W L hm hW2 z hz 0 x
    have hnx := hnn W L x
    calc ‖Γ.val (detData (Smat P.ψ W L) z (sigUpTo Sig (Smat P.ψ W L) z n)) ![0, x]‖
        = ‖Γ'.val (detData (Smat P.ψ W L) z (sigUpTo Sig (Smat P.ψ W L) z n)) ![0, x]‖ := by
          rw [hval]
      _ ≤ Γ'.absVal (detData (Smat P.ψ W L) z (sigUpTo Sig (Smat P.ψ W L) z n)) ![0, x] :=
          norm_val_le_absVal _ _ _ _ _ _
      _ = Γ'.absVal (detData (Smat P.ψ W L) z (sigMat Sig (Smat P.ψ W L) z)) ![0, x] :=
          absVal_sigUpTo Γ' _ _ _ n hK _
      _ ≤ _ := hb
      _ ≤ _ := by
          by_cases hx : x = 0
          · subst hx
            simp only [ite_true]
            nlinarith [mul_nonneg (hite W) hnx]
          · have h0 : (0 : Zd d L) ≠ x := fun h => hx h.symm
            simp only [h0, hx, ite_false]
            nlinarith [mul_nonneg (hite W) hnx]

/-- The bound of `graph_bound` for a formal sum of graphs of the shape, with one `W₀` and the
number of graphs as a factor. -/
theorem list_bound :
    ∀ (d : ℕ), 6 ≤ d → ∀ (P : Profile d) (c₀ c₁ κ ε : ℝ), 0 < c₀ → 0 < c₁ → c₀ + c₁ < 1 →
    0 < κ → 0 < ε → ∀ (n : ℕ) (Sig : ℕ → Expansion 2),
      SelfEnergiesUpTo d (smatVar P) Sig (n - 1) → ∀ τ : ℝ, 0 < τ →
      ∀ E : Expansion 2, (∀ g ∈ E, SelfEnergyShape n [g]) → ∃ W₀ : ℝ,
          ∀ (W L : ℕ) [NeZero L], (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ z ∈ specDom κ ε W L,
            ∀ x : Zd d L,
              ‖Expansion.val E
                  (detData (smatVar P W L) z (sigUpTo Sig (smatVar P W L) z n)) ![0, x]‖ ≤
                (E.length : ℝ) * ((W : ℝ) ^ τ *
                  ((W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
                  (if x = 0 then (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) else 0))) := by
  intro d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε n Sig hSig τ hτ E
  induction E with
  | nil =>
    intro _
    refine ⟨0, fun W L _ _ _ z _ x => ?_⟩
    simp [Expansion.val]
  | cons g E ih =>
    intro hE
    obtain ⟨W₁, h1⟩ := ih fun g' hg' => hE g' (List.mem_cons_of_mem _ hg')
    obtain ⟨m, Γ⟩ := g
    obtain ⟨W₂, h2⟩ := graph_bound d hd P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε n Sig hSig m Γ
      (hE _ (List.mem_cons_self ..)) τ hτ
    refine ⟨max W₁ W₂, fun W L _ hm hW z hz x => ?_⟩
    have a := h1 W L hm ((le_max_left _ _).trans hW) z hz x
    have b := h2 W L hm ((le_max_right _ _).trans hW) z hz x
    have hv : Expansion.val ((⟨m, Γ⟩ : Σ n : ℕ, Graph 2 n) :: E)
        (detData (smatVar P W L) z (sigUpTo Sig (smatVar P W L) z n)) ![0, x] =
        Γ.val (detData (smatVar P W L) z (sigUpTo Sig (smatVar P W L) z n)) ![0, x] +
        Expansion.val E (detData (smatVar P W L) z (sigUpTo Sig (smatVar P W L) z n)) ![0, x] := by
      simp [Expansion.val]
    rw [hv, List.length_cons, Nat.cast_succ]
    calc _ ≤ ‖Γ.val (detData (smatVar P W L) z (sigUpTo Sig (smatVar P W L) z n)) ![0, x]‖ +
          ‖Expansion.val E (detData (smatVar P W L) z (sigUpTo Sig (smatVar P W L) z n)) ![0, x]‖ :=
          norm_add_le _ _
      _ ≤ _ := by linarith

end Entrywise

/-- **The entrywise bound for `Σ_n`** ([I, (1.26)] with the diagonal term): see
`G13.entrywiseStmt`. The graphs of `Σ_n` are replaced by graphs of the same value that are normal
regular with `x`, `y` internal or diagonal (`G13.dotContract`), bounded by `detBound` and
`G13.diagBound` (`Entrywise.graph_bound`, `Entrywise.list_bound`); the factors `W^{τ/2}` and the
number of graphs are at most `L^{τ/2}` each for `L ≥ L₀`. -/
theorem G13.entrywise : G13.entrywiseStmt := by
  intro d hd P n Sig hn hSig hsh κ ε c₀ c₁ hκ hε hc₀ hc₁ hc τ hτ
  have hE : ∀ g ∈ Sig n, SelfEnergyShape n [g] := fun g hg g' hg' => by
    rw [List.mem_singleton] at hg'
    rw [hg']
    exact hsh g hg
  obtain ⟨W₀, h⟩ := Entrywise.list_bound d (by omega) P c₀ c₁ κ ε hc₀ hc₁ hc hκ hε n Sig hSig
    (τ / 2) (half_pos hτ) (Sig n) hE
  set m : ℕ := (Sig n).length with hm
  refine ⟨⌈(max W₀ 0) ^ (1 / c₁)⌉₊ + ⌈(m : ℝ) ^ (2 / τ)⌉₊, fun W L _ hL hadm z hz x => ?_⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hLc : (⌈(max W₀ 0) ^ (1 / c₁)⌉₊ : ℝ) ≤ L := by
    exact_mod_cast (Nat.le_add_right _ _).trans hL
  have hLm : (⌈(m : ℝ) ^ (2 / τ)⌉₊ : ℝ) ≤ L := by
    exact_mod_cast (Nat.le_add_left _ _).trans hL
  have hW0 : W₀ ≤ W := by
    have h1 : (max W₀ 0) ^ (1 / c₁) ≤ L := (Nat.le_ceil _).trans hLc
    have h2 : ((max W₀ 0) ^ (1 / c₁)) ^ c₁ ≤ (L : ℝ) ^ c₁ :=
      Real.rpow_le_rpow (by positivity) h1 hc₁.le
    rw [← Real.rpow_mul (le_max_right _ _), one_div_mul_cancel hc₁.ne', Real.rpow_one] at h2
    exact (le_max_left _ _).trans (h2.trans hadm.1)
  have hWL : (W : ℝ) ≤ L := by
    refine hadm.2.trans ?_
    calc (L : ℝ) ^ (1 - c₀) ≤ (L : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = L := Real.rpow_one _
  have hmL : (m : ℝ) ≤ (L : ℝ) ^ (τ / 2) := by
    have h1 : (m : ℝ) ^ (2 / τ) ≤ L := (Nat.le_ceil _).trans hLm
    have h2 : ((m : ℝ) ^ (2 / τ)) ^ (τ / 2) ≤ (L : ℝ) ^ (τ / 2) :=
      Real.rpow_le_rpow (by positivity) h1 (by positivity)
    rwa [← Real.rpow_mul (Nat.cast_nonneg _), show 2 / τ * (τ / 2) = 1 by field_simp,
      Real.rpow_one] at h2
  have hWp : (W : ℝ) ^ (τ / 2) ≤ (L : ℝ) ^ (τ / 2) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hWL (by positivity)
  have hLτ : (L : ℝ) ^ τ = (L : ℝ) ^ (τ / 2) * (L : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add hL0]; congr 1; ring
  have hb := h W L hadm hW0 z hz x
  have hR : 0 ≤ (W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
      (if x = 0 then (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) else 0) := by
    split_ifs <;> positivity
  have hmW : (m : ℝ) * (W : ℝ) ^ (τ / 2) ≤ (L : ℝ) ^ τ := by
    rw [hLτ]
    exact mul_le_mul hmL hWp (by positivity) (by positivity)
  have hfin : (L : ℝ) ^ τ * (W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
      (if x = 0 then (L : ℝ) ^ τ * (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) else 0) =
      (L : ℝ) ^ τ * ((W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
        (if x = 0 then (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) else 0)) := by
    split_ifs <;> ring
  rw [hfin]
  calc ‖sigMat Sig (smatVar P W L) z n 0 x‖
      ≤ (m : ℝ) * ((W : ℝ) ^ (τ / 2) * ((W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
          (if x = 0 then (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) else 0))) := hb
    _ = ((m : ℝ) * (W : ℝ) ^ (τ / 2)) * ((W : ℝ) ^ (-(((n : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
          (if x = 0 then (W : ℝ) ^ (-(((n : ℝ) - 2) * d / 2)) else 0)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hmW hR

end RBM8D.Graphs
