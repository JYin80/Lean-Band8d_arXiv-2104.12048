module

public import RBM8D.SelfEnergy.ValZ
public import RBM8D.SelfEnergy.Diag
public import Batteries.Tactic.OpenPrivate
public import RBM8D.Bound.AuxTreeZ
public import RBM8D.Kernel.Sinf
import all RBM8D.SelfEnergy.Diag
import all RBM8D.SelfEnergy.ValZ
import all RBM8D.Bound.AuxTreeZ
import all RBM8D.Kernel.Sinf

@[expose] public section

/-!
# The renormalized self-energies on `ℤ^d` ([I, Lemma 8.4, (8.6)–(8.7)], [I, Def 8.2])

On `ℤ^d` with `S_∞ = Sinf ψ W` ([I, (7.3)]), `Σ^{(r),∞}_l = ValZ.sigR` and the label kernels
`Σ̊^∞_l = ValZ.sigKer` of [I, Def 8.2]; `⟨x⟩ = |x|_∞ + W`.

* `InfBound.diagBound`: [I, Def 2.13 (i)] on `ℤ^d`: a diagonal graph with the shape of an `l`-th
  order self-energy has `|Γ^∞|^{abs}_{xy} ≤ 1_{x=y} W^{-(l-2)d/2} W^τ`, uniformly in `|E| < 2 − κ`.
* `InfBound.selUnif`: for `d ≥ 6` the label kernels `Σ̊^∞_l` satisfy [I, (2.13), (2.14), (2.16)]
  (`KerInfHyp`, with the diagonal term `W^{-(l-2)d/2} W^τ 1_{x=0}`) at every even `l ∈ [4, N]`,
  along every choice of energies `|E(W)| < 2 − κ` (`ValZ.SelUnif`).
* `InfBound.sigRBound`: [I, (8.7)] for `Σ^{(r),∞}_l` with the diagonal term:
  `|Σ^{(r),∞}_l(0, x)| ≤ W^{-ld/2} W^{2d-4} ⟨x⟩^{-(2d-4-τ)} + 1_{x=0} W^{-(l-2)d/2} W^τ`, summable,
  with `Σ_x |Σ^{(r),∞}_l(0, x)| ≤ W^{-(l-2)d/2} W^τ`, with `W₀` uniform in `|E| < 2 − κ`.
* `InfBound.sigKerBound`: the same pointwise bound and summability for `Σ̊^∞_l`.
* `InfBound.symbolBound`: for `d ≥ 8`, the symbol `ψ_{Σ̊^∞_l}(p) = Σ_x Σ̊^∞_l(0, x) e^{ip·x}`
  satisfies `|ψ_{Σ̊^∞_l}(p)| ≤ C W^τ W^{-(l-2)d/2} W² ‖p‖²` on `[−π, π]^d` (`‖p‖` the sup norm),
  uniformly in `|E| < 2 − κ`: the row sum of `Σ̊^∞_l` is `0` and `Σ̊^∞_l` is even ([I, Def 8.2],
  text after (8.3)), and its second moment is finite for `d > 6 + τ`.

The proofs go by induction on the order: the labelled `Θ` edges of `Σ^{(r),∞}_l` read `Σ̊^∞` of the
lower orders, so [I, Cor 7.6] on `ℤ^d` (`ValZ.corBound`) applies to the graphs of order `l` after
the contraction of [I, Def 3.1] (`G13.dotContract'`); a diagonal graph is reduced to one with the
external atoms identified, or to two copies of its loops.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace RBM8D

open Graphs

open private Diag_double Diag_redir Diag_double_internal Diag_ord_double Diag_double_isDetKind
  Diag_elim_cons Diag_kind from RBM8D.SelfEnergy.Diag
open private ValZ_coeff_bound from RBM8D.SelfEnergy.ValZ
open private latSum from RBM8D.Bound.AuxTreeZ
open private phiW_eq_re from RBM8D.Kernel.Sinf

variable {d : ℕ}

/-! ## Elementary bounds -/

/-- The first term of [I, (8.7)]: `W^{-ld/2} W^{2d-4} ⟨x⟩^{-(2d-4-τ)}`. -/
private def InfBound_A (d l W : ℕ) (τ : ℝ) (x : Fin d → ℤ) : ℝ :=
  (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
    ((zdInf x : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - τ))

/-- The diagonal term `W^{-(l-2)d/2} W^τ`. -/
private def InfBound_J (d l W : ℕ) (τ : ℝ) : ℝ :=
  (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ τ

private theorem InfBound_br_pos {W : ℕ} (hW : 1 ≤ W) (x : Fin d → ℤ) :
    0 < (zdInf x : ℝ) + W := by
  have : (1 : ℝ) ≤ W := by exact_mod_cast hW
  positivity

private theorem InfBound_W_le_br (W : ℕ) (x : Fin d → ℤ) : (W : ℝ) ≤ (zdInf x : ℝ) + W := by
  have := Nat.cast_nonneg (α := ℝ) (zdInf x)
  linarith

private theorem InfBound_A_nonneg {l W : ℕ} (hW : 1 ≤ W) (τ : ℝ) (x : Fin d → ℤ) :
    0 ≤ InfBound_A d l W τ x := by
  have h0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have := InfBound_br_pos hW x
  unfold InfBound_A
  positivity

private theorem InfBound_J_nonneg (l W : ℕ) (τ : ℝ) : 0 ≤ InfBound_J d l W τ := by
  have h0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  unfold InfBound_J
  positivity

/-- `A_{τ'}(x) W^a ≤ A_τ(x)` for `τ' + a ≤ τ`, `a ≥ 0`: `W ≤ ⟨x⟩`. -/
private theorem InfBound_A_mul_le {l W : ℕ} (hW : 1 ≤ W) {τ' a τ : ℝ} (ha : 0 ≤ a)
    (h : τ' + a ≤ τ) (x : Fin d → ℤ) :
    InfBound_A d l W τ' x * (W : ℝ) ^ a ≤ InfBound_A d l W τ x := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hb := InfBound_br_pos hW x
  have hWb := InfBound_W_le_br W x
  unfold InfBound_A
  set b := (zdInf x : ℝ) + W
  have h1 : (W : ℝ) ^ a ≤ b ^ a := Real.rpow_le_rpow (by positivity) hWb ha
  have h2 : b ^ (-(2 * (d : ℝ) - 4 - τ')) * b ^ a ≤ b ^ (-(2 * (d : ℝ) - 4 - τ)) := by
    rw [← Real.rpow_add hb]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h3 : (0 : ℝ) ≤ (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) := by
    positivity
  calc (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
          b ^ (-(2 * (d : ℝ) - 4 - τ')) * (W : ℝ) ^ a
      ≤ (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
          b ^ (-(2 * (d : ℝ) - 4 - τ')) * b ^ a := by gcongr
    _ = (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
          (b ^ (-(2 * (d : ℝ) - 4 - τ')) * b ^ a) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 h3

/-- `J_{τ'} W^a ≤ J_τ` for `τ' + a ≤ τ`. -/
private theorem InfBound_J_mul_le {l W : ℕ} (hW : 1 ≤ W) {τ' a τ : ℝ} (h : τ' + a ≤ τ) :
    InfBound_J d l W τ' * (W : ℝ) ^ a ≤ InfBound_J d l W τ := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  unfold InfBound_J
  rw [mul_assoc, ← Real.rpow_add hW0]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hW1 h) (by positivity)

/-- A constant is below `W^a` for `W ≥ C^{1/a}`. -/
private theorem InfBound_const_le {C a W : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hW : C ^ (1 / a) ≤ W) :
    C ≤ W ^ a := by
  calc C = (C ^ (1 / a)) ^ a := by
        rw [← Real.rpow_mul hC, one_div, inv_mul_cancel₀ ha.ne', Real.rpow_one]
    _ ≤ W ^ a := Real.rpow_le_rpow (Real.rpow_nonneg hC _) hW ha.le

/-- The lattice sum of `A_τ`: `Σ_x A_τ(x) ≤ C_L J_τ` with `C_L` the constant of
`Σ_v ⟨v⟩^{-γ} ≤ C_L W^{d-γ}` at `γ = 2d − 4 − τ > d`. -/
private theorem InfBound_A_sum {l W : ℕ} (hW : 1 ≤ W) {τ CL : ℝ}
    (hL : Summable (fun v : Fin d → ℤ => ((zdInf v : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - τ))) ∧
      ∑' v : Fin d → ℤ, ((zdInf v : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - τ)) ≤
        CL * (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 4 - τ))) :
    Summable (InfBound_A d l W τ) ∧ ∑' x, InfBound_A d l W τ x ≤ CL * InfBound_J d l W τ := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  refine ⟨hL.1.mul_left _, ?_⟩
  unfold InfBound_A InfBound_J
  rw [tsum_mul_left]
  calc (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
        ∑' v : Fin d → ℤ, ((zdInf v : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - τ))
      ≤ (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
          (CL * (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 4 - τ))) :=
        mul_le_mul_of_nonneg_left hL.2 (by positivity)
    _ = CL * ((W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
          (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 4 - τ))) := by ring
    _ = CL * ((W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ τ) := by
        rw [← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
        congr 2
        ring

/-- A threshold for every member of a finite list. -/
private theorem InfBound_W₀_list {α : Type*} (L : List α) (Q : α → ℕ → Prop)
    (h : ∀ g ∈ L, ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → Q g W) :
    ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ g ∈ L, Q g W := by
  induction L with
  | nil => exact ⟨0, fun _ _ g hg => absurd hg List.not_mem_nil⟩
  | cons a L ih =>
    obtain ⟨W₁, h₁⟩ := h a List.mem_cons_self
    obtain ⟨W₂, h₂⟩ := ih fun g hg => h g (List.mem_cons_of_mem a hg)
    refine ⟨max W₁ W₂, fun W hW g hg => ?_⟩
    rcases List.mem_cons.1 hg with rfl | hg
    · exact h₁ W ((le_max_left _ _).trans hW)
    · exact h₂ W ((le_max_right _ _).trans hW) g hg

/-- A sum over the labellings of no internal atom is the value at the empty labelling. -/
private theorem InfBound_fin_zero {X : Type*} (f : (Fin 0 → X) → ℝ) :
    Summable f ∧ ∑' σ, f σ = f Fin.elim0 := by
  have h : HasSum f (f Fin.elim0) :=
    hasSum_single Fin.elim0 fun σ hσ => (hσ (Subsingleton.elim _ _)).elim
  exact ⟨h.summable, h.tsum_eq⟩

/-! ## The diagonal graphs on `ℤ^d` -/

/-- The factor of a dotted edge between `x` and `y` is `1(x = y)`. -/
private theorem InfBound_compVal_dot {n : ℕ} (D : ValZ.Rec d) (s : Fin n → Fin d → ℤ)
    (x y : Fin d → ℤ) (c : Comp (Atom 2 n)) (hk : c.kind = .dot)
    (hxy : c.x = .inl 0 ∧ c.y = .inl 1 ∨ c.x = .inl 1 ∧ c.y = .inl 0) :
    ValZ.compVal D (Sum.elim ![x, y] s) c = if x = y then 1 else 0 := by
  obtain ⟨κ, a, b, mi, lab⟩ := c
  simp only at hk hxy
  subst hk
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [ValZ.compVal]
  · by_cases h : x = y
    · simp [ValZ.compVal, h]
    · simp [ValZ.compVal, h, Ne.symm h]

/-- A graph with a dotted edge between `x` and `y` has the summand `0` at `x ≠ y`. -/
private theorem InfBound_term_ne {n : ℕ} (Γ : Graph 2 n) {c : Comp (Atom 2 n)} (hc : c ∈ Γ.comps)
    (hk : c.kind = .dot) (hxy : c.x = .inl 0 ∧ c.y = .inl 1 ∨ c.x = .inl 1 ∧ c.y = .inl 0)
    (D : ValZ.Rec d) {x y : Fin d → ℤ} (hne : x ≠ y) (s : Fin n → Fin d → ℤ) :
    ValZ.term Γ D (Sum.elim ![x, y] s) = 0 := by
  unfold ValZ.term
  rw [List.prod_eq_zero, mul_zero]
  exact List.mem_map.2 ⟨c, hc, by rw [InfBound_compVal_dot D s x y c hk hxy]; simp [hne]⟩

/-- A normal graph without solid edges and with a `×`-dotted edge has the summand `0`: the
`×`-dotted edge is a loop. -/
private theorem InfBound_term_xdot {n C : ℕ} (Γ : Graph 2 n) (hN : Γ.Normal C)
    (hs : ∀ c ∈ Γ.comps, c.kind.isSolid = false) {c : Comp (Atom 2 n)} (hc : c ∈ Γ.comps)
    (hk : c.kind = .xdot) (D : ValZ.Rec d) (σ : Atom 2 n → Fin d → ℤ) :
    ValZ.term Γ D σ = 0 := by
  have hxy : c.x = c.y := by
    by_contra hne
    obtain ⟨c', hc', hs', -⟩ := (hN.2.2 c.x c.y hne).1 ⟨c, hc, hk, Or.inl ⟨rfl, rfl⟩⟩
    rw [hs c' hc'] at hs'
    exact absurd hs' (by decide)
  unfold ValZ.term
  rw [List.prod_eq_zero, mul_zero]
  refine List.mem_map.2 ⟨c, hc, ?_⟩
  obtain ⟨κ, a, b, mi, lab⟩ := c
  simp only at hk hxy
  subst hk hxy
  simp [ValZ.compVal]

/-- At `x = y`, the summand of a graph with a dotted edge between `x` and `y` at the labelling
`(b, t)` of its internal atoms is the summand of `Diag.graph Γ i` at `(x, b)` and `t`. -/
private theorem InfBound_term_cons {m : ℕ} (Γ : Graph 2 (m + 1)) (i : ℕ)
    (hi : i < Γ.comps.length) (hk : Γ.comps[i].kind = .dot)
    (hxy : Γ.comps[i].x = .inl 0 ∧ Γ.comps[i].y = .inl 1 ∨
      Γ.comps[i].x = .inl 1 ∧ Γ.comps[i].y = .inl 0)
    (D : ValZ.Rec d) (x b : Fin d → ℤ) (t : Fin m → Fin d → ℤ) :
    ValZ.term Γ D (Sum.elim ![x, x] (Fin.cons (α := fun _ => Fin d → ℤ) b t)) =
      ValZ.term (Diag.graph Γ i) D (Sum.elim ![x, b] t) := by
  have hperm := List.getElem_cons_eraseIdx_perm hi
  unfold ValZ.term
  rw [← (hperm.map (ValZ.compVal D _)).prod_eq, List.map_cons, List.prod_cons,
    InfBound_compVal_dot D _ x x _ hk hxy, ite_eq_left rfl, one_mul, Diag_elim_cons]
  simp only [Diag.graph, List.map_map]
  rfl

/-- At `x = y`, the summand of the doubled graph is the square of the summand of a graph without
internal atoms. -/
private theorem InfBound_term_double (Γ : Graph 2 0) (i : ℕ) (hi : i < Γ.comps.length)
    (hk : Γ.comps[i].kind = .dot)
    (hxy : Γ.comps[i].x = .inl 0 ∧ Γ.comps[i].y = .inl 1 ∨
      Γ.comps[i].x = .inl 1 ∧ Γ.comps[i].y = .inl 0)
    (D : ValZ.Rec d) (x : Fin d → ℤ) (σ : Fin 0 → Fin d → ℤ) :
    ValZ.term (Diag_double Γ i) D (Sum.elim ![x, x] σ) =
      ValZ.term Γ D (Sum.elim ![x, x] σ) ^ 2 := by
  have hσ : ∀ u : Atom 2 0, Sum.elim ![x, x] σ u = x := by
    rintro (a | a)
    · fin_cases a <;> rfl
    · exact a.elim0
  have hred : ∀ c, ValZ.compVal D (Sum.elim ![x, x] σ) (Diag_redir c) =
      ValZ.compVal D (Sum.elim ![x, x] σ) c := by
    intro c
    obtain ⟨κ, a, b, mi, lab⟩ := c
    simp only [ValZ.compVal, Diag_redir, hσ]
  unfold ValZ.term
  rw [← ((List.getElem_cons_eraseIdx_perm hi).map (ValZ.compVal D _)).prod_eq, List.map_cons,
    List.prod_cons, InfBound_compVal_dot D σ x x _ hk hxy, ite_eq_left rfl, one_mul]
  simp only [Diag_double, List.map_append, List.prod_append, List.map_map, Function.comp_def,
    hred, Coeff.eval, map_mul]
  ring


private theorem InfBound_zdInf_zero : zdInf (0 : Fin d → ℤ) = 0 := by
  simp [zdInf]

/-- `J_{τ'} ≤ J_τ` for `τ' ≤ τ`. -/
private theorem InfBound_J_mono {l W : ℕ} (hW : 1 ≤ W) {τ' τ : ℝ} (h : τ' ≤ τ) :
    InfBound_J d l W τ' ≤ InfBound_J d l W τ := by
  have := InfBound_J_mul_le (d := d) (l := l) hW (τ' := τ') (a := 0) (τ := τ) (by linarith)
  rwa [Real.rpow_zero, mul_one] at this

/-- The absolute value of a graph without internal atoms is the norm of its summand. -/
private theorem InfBound_absVal_zero (G : Graph 2 0) (D : ValZ.Rec d) (e : Fin 2 → Fin d → ℤ) :
    ValZ.absVal G D e = ‖ValZ.term G D (Sum.elim e Fin.elim0)‖ :=
  (InfBound_fin_zero _).2

/-- The diagonal bound at `x = y` for a diagonal graph with an internal atom: the external atoms
are identified and the internal atom `0` becomes the external atom `y` (`Diag.graph`); [I, Cor 7.6]
on `ℤ^d` for that graph and `Σ_b ⟨x − b⟩^{-(2d-4-τ')} ≲ W^{d-(2d-4-τ')}`. -/
private theorem InfBound_diag_succ (hd : 6 ≤ d) (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ)
    (cψ c' : ℝ) (hψ : ProfileShape ψ cψ) (hψ' : SymbolBound ψ c') (C : ℕ → ℝ) {κ : ℝ}
    (hκ : 0 < κ) {l : ℕ} (K : ℝ → KerInf d) (hK : ValZ.SelUnif κ (l - 1) K) {m : ℕ}
    (Γ : Graph 2 (m + 1)) (hKd : Γ.comps.all (Comp.isDetKind (l - 1)) = true)
    (hO : Γ.ord = l) (hD : G13.IsDiag Γ) (hA : Γ.DotsAcyclic)
    (hX : ∀ c ∈ Γ.comps, c.kind ≠ .xdot) (hDC : Γ.internalize.DoublyConnected) (τ : ℝ)
    (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ E : ℝ, |E| < 2 - κ → ∀ x : Fin d → ℤ,
        Summable (fun σ : Fin (m + 1) → Fin d → ℤ =>
          ‖ValZ.term Γ (ValZ.rec s (K E) W E) (Sum.elim ![x, x] σ)‖) ∧
        ValZ.absVal Γ (ValZ.rec s (K E) W E) ![x, x] ≤ InfBound_J d l W τ := by
  obtain ⟨i, hi, hk, hrest⟩ := Diag.dot_unique Γ hD hA
  have hxy := hD.2 _ (List.getElem_mem hi) hk
  have hKc : ∀ c ∈ Γ.comps, c.isDetKind (l - 1) = true := List.all_eq_true.1 hKd
  have hrest' : ∀ c ∈ Γ.comps.eraseIdx i,
      c.kind ≠ .dot ∧ c.kind ≠ .xdot ∧ c.kind.isSolid = false := fun c hc =>
    ⟨hrest c hc, hX c (List.mem_of_mem_eraseIdx hc),
      (Diag_kind c (hKc c (List.mem_of_mem_eraseIdx hc))).1⟩
  obtain ⟨hN', hDC'⟩ := Diag.internal Γ i hi hk hD hrest' hDC
  set G := Diag.graph Γ i with hGdef
  have hOG : (((G.ord : ℤ) : ℝ)) = (l : ℝ) := by
    rw [hGdef, Diag.ord_eq Γ i hi hk, hO]
    push_cast
    ring
  set τ' := min τ 1 / 2 with hτ'def
  have hτ1 : 0 < min τ 1 := lt_min hτ one_pos
  have hτ' : 0 < τ' := by positivity
  have hτ'2 : τ' + τ' ≤ τ := by
    have := min_le_left τ 1
    linarith
  have hτ'1 : τ' ≤ 1 / 2 := by
    have := min_le_right τ 1
    linarith
  obtain ⟨W₁, hW₁⟩ := ValZ.corBound d hd ψ cψ c' hψ hψ' C κ hκ (l - 1) K hK m _ G hN' hDC'
    (Diag.all_isDetKind Γ i _ hKd) τ' hτ'
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨CL, hCL, hL⟩ := latSum d (2 * d - 4 - τ') (by linarith)
  refine ⟨max W₁ (max 1 (CL ^ (1 / τ'))), fun W hW s hs E hE x => ?_⟩
  have hW1' : (1 : ℝ) ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hW)
  have hW1 : 1 ≤ W := by exact_mod_cast hW1'
  have hCW : CL ≤ (W : ℝ) ^ τ' :=
    InfBound_const_le hCL hτ' (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hW))
  set D := ValZ.rec s (K E) W E with hDdef
  have hb : ∀ b, Summable (fun t : Fin m → Fin d → ℤ => ‖ValZ.term G D (Sum.elim ![x, b] t)‖) ∧
      ValZ.absVal G D ![x, b] ≤ InfBound_A d l W τ' (x - b) := by
    intro b
    obtain ⟨h1, h2⟩ := hW₁ W (le_trans (le_max_left _ _) hW) s hs E hE x b
    refine ⟨h1, ?_⟩
    rw [hOG] at h2
    exact h2
  obtain ⟨hA1, hA2⟩ := InfBound_A_sum (d := d) (l := l) hW1 (hL W hW1)
  have hsA : Summable (fun b => InfBound_A d l W τ' (x - b)) :=
    (Equiv.subLeft x).summable_iff.2 hA1
  have htA : ∑' b, InfBound_A d l W τ' (x - b) = ∑' v, InfBound_A d l W τ' v :=
    (Equiv.subLeft x).tsum_eq (InfBound_A d l W τ')
  set F : (Fin d → ℤ) × (Fin m → Fin d → ℤ) → ℝ :=
    fun p => ‖ValZ.term G D (Sum.elim ![x, p.1] p.2)‖ with hFdef
  have hFs : Summable F := by
    refine (summable_prod_of_nonneg (fun p => norm_nonneg _)).2 ⟨fun b => (hb b).1, ?_⟩
    exact Summable.of_nonneg_of_le (fun b => tsum_nonneg fun t => norm_nonneg _)
      (fun b => (hb b).2) hsA
  have he : ∀ p : (Fin d → ℤ) × (Fin m → Fin d → ℤ),
      ‖ValZ.term Γ D (Sum.elim ![x, x] ((Fin.consEquiv fun _ => Fin d → ℤ) p))‖ = F p := by
    rintro ⟨b, t⟩
    simp only [Fin.consEquiv_apply, hFdef]
    rw [InfBound_term_cons Γ i hi hk hxy D x b t]
  refine ⟨?_, ?_⟩
  · rw [← (Fin.consEquiv fun _ => Fin d → ℤ).summable_iff]
    exact hFs.congr fun p => (he p).symm
  · unfold ValZ.absVal
    rw [← (Fin.consEquiv fun _ => Fin d → ℤ).tsum_eq]
    simp_rw [he]
    rw [hFs.tsum_prod]
    calc ∑' b, ∑' t, F (b, t) = ∑' b, ValZ.absVal G D ![x, b] := rfl
      _ ≤ ∑' b, InfBound_A d l W τ' (x - b) :=
          (Summable.of_nonneg_of_le (fun b => tsum_nonneg fun t => norm_nonneg _)
            (fun b => (hb b).2) hsA).tsum_le_tsum (fun b => (hb b).2) hsA
      _ ≤ CL * InfBound_J d l W τ' := by rw [htA]; exact hA2
      _ ≤ (W : ℝ) ^ τ' * InfBound_J d l W τ' :=
          mul_le_mul_of_nonneg_right hCW (InfBound_J_nonneg _ _ _)
      _ ≤ InfBound_J d l W τ := by
          rw [mul_comm]
          exact InfBound_J_mul_le hW1 hτ'2

/-- The diagonal bound at `x = y` for a diagonal graph without internal atoms: its other
components are loops at `x = y`; two copies of them, each joining `x` and `y`, form a graph of
order `2l − 4` to which [I, Cor 7.6] on `ℤ^d` applies at `x = y`, and the bound is the square root
of that bound. If the dotted edge is the only component, `l = 2` and the coefficient is bounded. -/
private theorem InfBound_diag_zero (hd : 6 ≤ d) (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ)
    (cψ c' : ℝ) (hψ : ProfileShape ψ cψ) (hψ' : SymbolBound ψ c') (C : ℕ → ℝ) {κ : ℝ}
    (hκ : 0 < κ) {l : ℕ} (K : ℝ → KerInf d) (hK : ValZ.SelUnif κ (l - 1) K)
    (Γ : Graph 2 0) (hKd : Γ.comps.all (Comp.isDetKind (l - 1)) = true) (hO : Γ.ord = l)
    (hD : G13.IsDiag Γ) (hA : Γ.DotsAcyclic) (hX : ∀ c ∈ Γ.comps, c.kind ≠ .xdot) (τ : ℝ)
    (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ E : ℝ, |E| < 2 - κ → ∀ x : Fin d → ℤ,
        ValZ.absVal Γ (ValZ.rec s (K E) W E) ![x, x] ≤ InfBound_J d l W τ := by
  obtain ⟨i, hi, hk, hrest⟩ := Diag.dot_unique Γ hD hA
  have hxy := hD.2 _ (List.getElem_mem hi) hk
  have hKc : ∀ c ∈ Γ.comps, c.isDetKind (l - 1) = true := List.all_eq_true.1 hKd
  by_cases hR : Γ.comps.eraseIdx i = []
  · have hperm := List.getElem_cons_eraseIdx_perm hi
    rw [hR] at hperm
    have hl : (l : ℝ) = 2 := by
      have h2 : Γ.ord = 2 := by
        unfold Graph.ord
        rw [← (hperm.map fun c => c.kind.ord).sum_eq]
        simp [hk, Kind.ord]
      have : (l : ℤ) = 2 := by rw [← hO, h2]
      exact_mod_cast this
    obtain ⟨Cc, hCc0, hCc⟩ := ValZ_coeff_bound hκ Γ.coeff
    refine ⟨max 1 (Cc ^ (1 / τ)), fun W hW s hs E hE x => ?_⟩
    have hterm : ValZ.term Γ (ValZ.rec s (K E) W E) (Sum.elim ![x, x] Fin.elim0) =
        Γ.coeff.eval (mE E) := by
      unfold ValZ.term
      rw [← (hperm.map (ValZ.compVal _ _)).prod_eq]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        InfBound_compVal_dot _ _ x x _ hk hxy, ↓reduceIte, mul_one]
      rfl
    rw [InfBound_absVal_zero, hterm]
    unfold InfBound_J
    rw [hl, sub_self, zero_mul, zero_div, neg_zero, Real.rpow_zero, one_mul]
    exact (hCc E hE).trans (InfBound_const_le hCc0 hτ (le_trans (le_max_right _ _) hW))
  · have hrestK : ∀ c ∈ Γ.comps.eraseIdx i,
        (∃ w, c.kind = .waved w) ∨ (∃ o, c.kind = .theta o) := fun c hc =>
      (Diag_kind c (hKc c (List.mem_of_mem_eraseIdx hc))).2 (hrest c hc)
        (hX c (List.mem_of_mem_eraseIdx hc))
    obtain ⟨hN₂, hDC₂⟩ := Diag_double_internal Γ i hrestK hR
    obtain ⟨W₀, hW₀⟩ := ValZ.corBound d hd ψ cψ c' hψ hψ' C κ hκ (l - 1) K hK 0 _
      (Diag_double Γ i) hN₂ hDC₂ (Diag_double_isDetKind Γ i _ hKd) τ hτ
    refine ⟨max W₀ 1, fun W hW s hs E hE x => ?_⟩
    have hW1' : (1 : ℝ) ≤ W := le_trans (le_max_right _ _) hW
    have hW1 : 1 ≤ W := by exact_mod_cast hW1'
    have hW0 : (0 : ℝ) < W := by linarith
    have h := (hW₀ W (le_trans (le_max_left _ _) hW) s hs E hE x x).2
    rw [InfBound_absVal_zero, InfBound_term_double Γ i hi hk hxy, norm_pow,
      Diag_ord_double Γ i hi hk, hO, sub_self, InfBound_zdInf_zero] at h
    have hsq : (W : ℝ) ^ (-((((2 * (l : ℤ) - 4 : ℤ)) : ℝ) * d / 2)) *
        (W : ℝ) ^ (2 * (d : ℝ) - 4) * (((0 : ℕ) : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - τ)) =
        InfBound_J d l W (τ / 2) ^ 2 := by
      unfold InfBound_J
      rw [Nat.cast_zero, zero_add, ← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0,
        ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
      congr 1
      push_cast
      ring
    rw [hsq] at h
    rw [InfBound_absVal_zero]
    exact ((pow_le_pow_iff_left₀ (norm_nonneg _) (InfBound_J_nonneg _ _ _) two_ne_zero).1 h).trans
      (InfBound_J_mono hW1 (by linarith))

/-- **[I, Def 2.13 (i)] on `ℤ^d`**: for `d ≥ 6`, a profile shape `ψ` with `−1 + c' ≤ ψ ≤ 1`, the
constants `C`, `κ > 0`, label kernels `K(E)` with `ValZ.SelUnif κ (l − 1) K` and a diagonal graph
`Γ` (its dotted edges join `x` and `y`) with the shape of an `l`-th order self-energy: for every
`τ > 0` there is `W₀` such that for `W ≥ W₀`, every kernel `s` of `InfKernel ψ C W`, `|E| < 2 − κ`
and `x, y ∈ ℤ^d`, the summand of the absolute value is summable and
`|Γ^∞|^{abs}_{xy} ≤ 1_{x=y} W^{-(l-2)d/2} W^τ`. -/
theorem InfBound.diagBound (hd : 6 ≤ d) (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ)
    (cψ c' : ℝ) (hψ : ProfileShape ψ cψ) (hψ' : SymbolBound ψ c') (C : ℕ → ℝ) {κ : ℝ}
    (hκ : 0 < κ) {l : ℕ} (K : ℝ → KerInf d) (hK : ValZ.SelUnif κ (l - 1) K) {n : ℕ}
    (Γ : Graph 2 n) (hΓ : SelfEnergyShape l [⟨n, Γ⟩]) (hD : G13.IsDiag Γ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ E : ℝ, |E| < 2 - κ → ∀ x y : Fin d → ℤ,
        Summable (fun σ : Fin n → Fin d → ℤ =>
          ‖ValZ.term Γ (ValZ.rec s (K E) W E) (Sum.elim ![x, y] σ)‖) ∧
        ValZ.absVal Γ (ValZ.rec s (K E) W E) ![x, y] ≤
          if x = y then (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ τ else 0 := by
  obtain ⟨⟨Cn, hN, hA⟩, hKd, hO, hDC⟩ := hΓ _ (List.mem_singleton_self _)
  have hKd : Γ.comps.all (Comp.isDetKind (l - 1)) = true := hKd
  have hO : Γ.ord = l := hO
  have hDC : Γ.internalize.DoublyConnected := hDC
  have hN : Γ.Normal Cn := hN
  have hA : Γ.DotsAcyclic := hA
  have hsol : ∀ c ∈ Γ.comps, c.kind.isSolid = false := fun c hc =>
    (Diag_kind c (List.all_eq_true.1 hKd c hc)).1
  obtain ⟨i, hi, hk, -⟩ := Diag.dot_unique Γ hD hA
  have hxy := hD.2 _ (List.getElem_mem hi) hk
  have hzero : ∀ (D : ValZ.Rec d) (x y : Fin d → ℤ),
      (∀ σ : Fin n → Fin d → ℤ, ValZ.term Γ D (Sum.elim ![x, y] σ) = 0) →
      Summable (fun σ : Fin n → Fin d → ℤ => ‖ValZ.term Γ D (Sum.elim ![x, y] σ)‖) ∧
        ValZ.absVal Γ D ![x, y] = 0 := by
    intro D x y h0
    refine ⟨?_, ?_⟩
    · simp only [h0, norm_zero]
      exact summable_zero
    · unfold ValZ.absVal
      simp only [h0, norm_zero, tsum_zero]
  have hJ0 : ∀ W : ℕ, 0 ≤ (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ τ := fun W =>
    InfBound_J_nonneg (d := d) l W τ
  by_cases hX : ∃ c ∈ Γ.comps, c.kind = .xdot
  · obtain ⟨c, hc, hck⟩ := hX
    refine ⟨0, fun W _ s _ E _ x y => ?_⟩
    obtain ⟨h1, h2⟩ := hzero (ValZ.rec s (K E) W E) x y fun σ =>
      InfBound_term_xdot Γ hN hsol hc hck _ _
    refine ⟨h1, ?_⟩
    rw [h2]
    split_ifs
    · exact hJ0 W
    · exact le_rfl
  replace hX : ∀ c ∈ Γ.comps, c.kind ≠ .xdot := fun c hc hck => hX ⟨c, hc, hck⟩
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ E : ℝ, |E| < 2 - κ → ∀ x : Fin d → ℤ,
        Summable (fun σ : Fin n → Fin d → ℤ =>
          ‖ValZ.term Γ (ValZ.rec s (K E) W E) (Sum.elim ![x, x] σ)‖) ∧
        ValZ.absVal Γ (ValZ.rec s (K E) W E) ![x, x] ≤ InfBound_J d l W τ := by
    cases n with
    | zero =>
      obtain ⟨W₀, h⟩ := InfBound_diag_zero hd ψ cψ c' hψ hψ' C hκ K hK Γ hKd hO hD hA hX τ hτ
      exact ⟨W₀, fun W hW s hs E hE x => ⟨(InfBound_fin_zero _).1, h W hW s hs E hE x⟩⟩
    | succ m =>
      exact InfBound_diag_succ hd ψ cψ c' hψ hψ' C hκ K hK Γ hKd hO hD hA hX hDC τ hτ
  refine ⟨W₀, fun W hW s hs E hE x y => ?_⟩
  by_cases hxy' : x = y
  · subst hxy'
    rw [ite_eq_left rfl]
    exact hW₀ W hW s hs E hE x
  · obtain ⟨h1, h2⟩ := hzero (ValZ.rec s (K E) W E) x y fun σ =>
      InfBound_term_ne Γ (List.getElem_mem hi) hk hxy _ hxy' σ
    exact ⟨h1, by rw [h2, ite_eq_right hxy']⟩


/-! ## [I, (8.7)] for `Σ^{(r),∞}_l` and `Σ̊^∞_l` -/

/-- One graph with the shape of an `l`-th order self-energy: after the contraction of
[I, Def 3.1] (`G13.dotContract'`) it is normal regular with `x`, `y` internal, and [I, Cor 7.6] on
`ℤ^d` applies, or it is diagonal (`InfBound.diagBound`). -/
private theorem InfBound_graph (hd : 6 ≤ d) (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ)
    (cψ c' : ℝ) (hψ : ProfileShape ψ cψ) (hψ' : SymbolBound ψ c') (C : ℕ → ℝ) {κ : ℝ}
    (hκ : 0 < κ) {l : ℕ} (K : ℝ → KerInf d) (hK : ValZ.SelUnif κ (l - 1) K) {n : ℕ}
    (Γ : Graph 2 n) (hΓ : SelfEnergyShape l [⟨n, Γ⟩]) (τ : ℝ) (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ E : ℝ, |E| < 2 - κ → ∀ x y : Fin d → ℤ,
        ‖ValZ.val Γ (ValZ.rec s (K E) W E) ![x, y]‖ ≤
          InfBound_A d l W τ (x - y) + (if x = y then InfBound_J d l W τ else 0) := by
  obtain ⟨n', Γ', hsh', -, hval, hcase⟩ := G13.dotContract' l n Γ hΓ
  have hI0 : ∀ (W : ℕ) (x y : Fin d → ℤ), 0 ≤ (if x = y then InfBound_J d l W τ else 0) := by
    intro W x y
    split_ifs
    · exact InfBound_J_nonneg _ _ _
    · exact le_rfl
  rcases hcase with ⟨C', hN'⟩ | hD'
  · obtain ⟨-, hKd', hO', hDC'⟩ := hsh' _ (List.mem_singleton_self _)
    obtain ⟨W₀, hW₀⟩ := ValZ.corBound d hd ψ cψ c' hψ hψ' C κ hκ (l - 1) K hK n' C' Γ' hN'
      hDC' hKd' τ hτ
    refine ⟨max W₀ 1, fun W hW s hs E hE x y => ?_⟩
    have hW1 : 1 ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
    obtain ⟨h1, h2⟩ := hW₀ W (le_trans (le_max_left _ _) hW) s hs E hE x y
    have hO'' : (((Γ'.ord : ℤ)) : ℝ) = (l : ℝ) := by
      have : Γ'.ord = (l : ℤ) := hO'
      rw [this]
      push_cast
      ring
    rw [hO''] at h2
    rw [← (hval d _ _).1]
    calc ‖ValZ.val Γ' (ValZ.rec s (K E) W E) ![x, y]‖
        ≤ ValZ.absVal Γ' (ValZ.rec s (K E) W E) ![x, y] := ValZ.norm_val_le _ _ _ h1
      _ ≤ InfBound_A d l W τ (x - y) := h2
      _ ≤ _ := le_add_of_nonneg_right (hI0 W x y)
  · obtain ⟨W₀, hW₀⟩ := InfBound.diagBound hd ψ cψ c' hψ hψ' C hκ K hK Γ' hsh' hD' τ hτ
    refine ⟨max W₀ 1, fun W hW s hs E hE x y => ?_⟩
    have hW1 : 1 ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
    obtain ⟨h1, h2⟩ := hW₀ W (le_trans (le_max_left _ _) hW) s hs E hE x y
    rw [← (hval d _ _).1]
    calc ‖ValZ.val Γ' (ValZ.rec s (K E) W E) ![x, y]‖
        ≤ ValZ.absVal Γ' (ValZ.rec s (K E) W E) ![x, y] := ValZ.norm_val_le _ _ _ h1
      _ ≤ (if x = y then InfBound_J d l W τ else 0) := h2
      _ ≤ _ := le_add_of_nonneg_left (InfBound_A_nonneg hW1 _ _)

/-- The value of a formal sum is at most its number of terms times a bound for each term. -/
private theorem InfBound_expVal_le (L : Expansion 2) (D : ValZ.Rec d) (e : Fin 2 → Fin d → ℤ)
    {B : ℝ} (h : ∀ g ∈ L, ‖ValZ.val g.2 D e‖ ≤ B) : ‖ValZ.expVal L D e‖ ≤ L.length * B := by
  induction L with
  | nil => simp [ValZ.expVal]
  | cons g L ih =>
    have h1 := h g List.mem_cons_self
    have h2 := ih fun g' hg' => h g' (List.mem_cons_of_mem g hg')
    have he : ValZ.expVal (g :: L) D e = ValZ.val g.2 D e + ValZ.expVal L D e := by
      simp [ValZ.expVal]
    rw [he, List.length_cons, Nat.cast_succ]
    calc ‖ValZ.val g.2 D e + ValZ.expVal L D e‖
        ≤ ‖ValZ.val g.2 D e‖ + ‖ValZ.expVal L D e‖ := norm_add_le _ _
      _ ≤ B + L.length * B := add_le_add h1 h2
      _ = (L.length + 1) * B := by ring

/-- The decay of a kernel of `InfKernel ψ C W` with `k = 2d − 4`:
`|s(x)| ≤ C_k W^{-d} W^{2d-4} ⟨x⟩^{-(2d-4)}`. -/
private theorem InfBound_decay {ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ} {C : ℕ → ℝ}
    {W : ℕ} {s : (Fin d → ℤ) → ℝ} (hs : InfKernel ψ C W s) (hW : 1 ≤ W) (hd : 2 ≤ d)
    (x : Fin d → ℤ) :
    |s x| ≤ max (C (2 * d - 4)) 0 * ((W : ℝ) ^ (-(d : ℝ)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
      ((zdInf x : ℝ) + W) ^ (-(2 * (d : ℝ) - 4))) := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hb := InfBound_br_pos hW x
  set b := (zdInf x : ℝ) + W with hbdef
  set k := 2 * d - 4 with hkdef
  have hk : (2 * (d : ℝ) - 4) = (k : ℝ) := by
    rw [hkdef, Nat.cast_sub (by omega : 4 ≤ 2 * d)]
    push_cast
    ring
  have h := hs.decay k x
  have h1 : (1 + (zdInf x : ℝ) / W) = b / W := by
    rw [hbdef]
    field_simp
    ring
  rw [h1, div_pow] at h
  have hbk : 0 < b ^ k := pow_pos hb _
  have hWk : 0 < (W : ℝ) ^ k := pow_pos hW0 _
  have hWd : 0 < (W : ℝ) ^ d := pow_pos hW0 _
  have h2 : |s x| ≤ (C k / (W : ℝ) ^ d) / (b ^ k / (W : ℝ) ^ k) :=
    (le_div_iff₀ (by positivity)).2 h
  have h3 : (C k / (W : ℝ) ^ d) / (b ^ k / (W : ℝ) ^ k) =
      C k * (((W : ℝ) ^ d)⁻¹ * (W : ℝ) ^ k * (b ^ k)⁻¹) := by
    field_simp
  rw [hk, Real.rpow_neg hW0.le, Real.rpow_neg hb.le, Real.rpow_natCast, Real.rpow_natCast,
    Real.rpow_natCast]
  calc |s x| ≤ C k * (((W : ℝ) ^ d)⁻¹ * (W : ℝ) ^ k * (b ^ k)⁻¹) := h3 ▸ h2
    _ ≤ max (C k) 0 * (((W : ℝ) ^ d)⁻¹ * (W : ℝ) ^ k * (b ^ k)⁻¹) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- `J_{τ'} W^{-d} W^{2d-4} ⟨x⟩^{-(2d-4)} ≤ A_{τ'}(x)`: `W^{-(l-2)d/2} W^{-d} = W^{-ld/2}` and
`W ≤ ⟨x⟩`. -/
private theorem InfBound_J_mul_B_le {l W : ℕ} (hW : 1 ≤ W) {τ' : ℝ} (hτ' : 0 ≤ τ')
    (x : Fin d → ℤ) :
    InfBound_J d l W τ' * ((W : ℝ) ^ (-(d : ℝ)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
      ((zdInf x : ℝ) + W) ^ (-(2 * (d : ℝ) - 4))) ≤ InfBound_A d l W τ' x := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hpow : (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ (-(d : ℝ)) =
      (W : ℝ) ^ (-((l : ℝ) * d / 2)) := by
    rw [← Real.rpow_add hW0]
    congr 1
    ring
  have heq : InfBound_J d l W τ' * ((W : ℝ) ^ (-(d : ℝ)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
      ((zdInf x : ℝ) + W) ^ (-(2 * (d : ℝ) - 4))) = InfBound_A d l W 0 x * (W : ℝ) ^ τ' := by
    unfold InfBound_J InfBound_A
    rw [sub_zero, ← hpow]
    ring
  rw [heq]
  exact InfBound_A_mul_le hW hτ' (by linarith) x

/-- `c (A_{τ'}(x) + 1_{x=0} J_{τ'}) ≤ A_τ(x) + 1_{x=0} J_τ` for `0 ≤ c ≤ W^{τ'}` and
`2τ' ≤ τ`. -/
private theorem InfBound_absorb {l W : ℕ} (hW : 1 ≤ W) {τ' τ c : ℝ}
    (hc : c ≤ (W : ℝ) ^ τ') (hτ' : 0 ≤ τ') (h : τ' + τ' ≤ τ) (x : Fin d → ℤ) :
    c * (InfBound_A d l W τ' x + (if x = 0 then InfBound_J d l W τ' else 0)) ≤
      InfBound_A d l W τ x + (if x = 0 then InfBound_J d l W τ else 0) := by
  rw [mul_add]
  refine add_le_add ?_ ?_
  · calc c * InfBound_A d l W τ' x ≤ (W : ℝ) ^ τ' * InfBound_A d l W τ' x :=
          mul_le_mul_of_nonneg_right hc (InfBound_A_nonneg hW _ _)
      _ = InfBound_A d l W τ' x * (W : ℝ) ^ τ' := mul_comm _ _
      _ ≤ InfBound_A d l W τ x := InfBound_A_mul_le hW hτ' h x
  · split_ifs
    · calc c * InfBound_J d l W τ' ≤ (W : ℝ) ^ τ' * InfBound_J d l W τ' :=
            mul_le_mul_of_nonneg_right hc (InfBound_J_nonneg _ _ _)
        _ = InfBound_J d l W τ' * (W : ℝ) ^ τ' := mul_comm _ _
        _ ≤ InfBound_J d l W τ := InfBound_J_mul_le hW h
    · simp

/-- The step of the induction at the order `l`: if the label kernels `Σ̊^∞` of the orders below
`l` satisfy `ValZ.SelUnif κ (l − 1)`, then [I, (8.7)] holds for `Σ^{(r),∞}_l` and `Σ̊^∞_l`, with
the row sum of `|Σ^{(r),∞}_l|`, uniformly in `|E| < 2 − κ`. -/
private theorem InfBound_level (hd : 6 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) {l : ℕ}
    (hl : 1 ≤ l) (hsh : SelfEnergyShape l (Sig l)) {κ : ℝ} (hκ : 0 < κ)
    (hK : ValZ.SelUnif κ (l - 1) (ValZ.sigKer Sig P.ψ)) (τ : ℝ) (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ →
      (∀ x, ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖ ≤
        InfBound_A d l W τ x + (if x = 0 then InfBound_J d l W τ else 0)) ∧
      Summable (fun x => ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖) ∧
      ∑' x, ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖ ≤ InfBound_J d l W τ ∧
      (∀ x, ‖ValZ.sigKer Sig P.ψ E l W x‖ ≤
        InfBound_A d l W τ x + (if x = 0 then InfBound_J d l W τ else 0)) ∧
      Summable (fun x => ‖ValZ.sigKer Sig P.ψ E l W x‖) := by
  have hψ : ProfileShape P.ψ P.cψ := ⟨P.cψ_pos, P.at_zero, P.le_max, P.symm⟩
  obtain ⟨c', hc'⟩ := symbolBound_of_profile d P
  obtain ⟨C, W₁, hC⟩ := Sinf_infKernel d P.ψ P.cψ hψ
  set τ' := min τ 1 / 2 with hτ'def
  have hτ1 : 0 < min τ 1 := lt_min hτ one_pos
  have hτ' : 0 < τ' := by positivity
  have hτ'2 : τ' + τ' ≤ τ := by
    have := min_le_left τ 1
    linarith
  have hτ'1 : τ' ≤ 1 / 2 := by
    have := min_le_right τ 1
    linarith
  have hdet : ∀ g ∈ Sig l, g.2.comps.all (Comp.isDetKind (l - 1)) = true :=
    fun g hg => (hsh g hg).2.1
  obtain ⟨W₂, hW₂⟩ := InfBound_W₀_list (Sig l) (fun g W => ∀ s : (Fin d → ℤ) → ℝ,
      InfKernel P.ψ C W s → ∀ E : ℝ, |E| < 2 - κ → ∀ x y : Fin d → ℤ,
        ‖ValZ.val g.2 (ValZ.rec s (ValZ.sigKer Sig P.ψ E) W E) ![x, y]‖ ≤
          InfBound_A d l W τ' (x - y) + (if x = y then InfBound_J d l W τ' else 0))
    (fun g hg => InfBound_graph hd P.ψ P.cψ c' hψ hc' C hκ (ValZ.sigKer Sig P.ψ) hK g.2
      (fun g' hg' => by
        rw [List.mem_singleton] at hg'
        subst hg'
        exact hsh g hg) τ' hτ')
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨CL, hCL, hL⟩ := latSum d (2 * d - 4 - τ') (by linarith)
  set g : ℝ := ((Sig l).length : ℝ) with hgdef
  have hg0 : 0 ≤ g := Nat.cast_nonneg _
  set Ck : ℝ := max (C (2 * d - 4)) 0 with hCkdef
  have hCk0 : 0 ≤ Ck := le_max_right _ _
  set c₁ : ℝ := g + g * (CL + 1) * Ck with hc₁def
  set T : ℝ := 2 * (g + 1) * (CL + 1) * (Ck + 1) with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hgc₁ : g ≤ c₁ := by
    rw [hc₁def]
    have : 0 ≤ g * (CL + 1) * Ck := by positivity
    linarith
  have hc₁T : c₁ ≤ T := by
    rw [hc₁def, hTdef]
    nlinarith [mul_nonneg (mul_nonneg hg0 (by linarith : (0 : ℝ) ≤ CL + 1)) hCk0,
      mul_nonneg hg0 hCL, mul_nonneg hCL hCk0, mul_nonneg (mul_nonneg hg0 hCL) hCk0]
  have hgCT : g * (CL + 1) ≤ T := by
    rw [hTdef]
    nlinarith [mul_nonneg (mul_nonneg hg0 (by linarith : (0 : ℝ) ≤ CL + 1)) hCk0,
      mul_nonneg hg0 hCL, mul_nonneg hCL hCk0, mul_nonneg (mul_nonneg hg0 hCL) hCk0]
  refine ⟨max (max W₁ W₂) (max 1 (T ^ (1 / τ'))), fun W hW E hE => ?_⟩
  have hW1' : (1 : ℝ) ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hW)
  have hW1 : 1 ≤ W := by exact_mod_cast hW1'
  have hTW : T ≤ (W : ℝ) ^ τ' :=
    InfBound_const_le hT0 hτ' (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hW))
  have hs := hC W (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW)
  have hI0 : ∀ x : Fin d → ℤ, 0 ≤ (if x = 0 then InfBound_J d l W τ' else 0) := by
    intro x
    split_ifs
    · exact InfBound_J_nonneg _ _ _
    · exact le_rfl
  have hpt : ∀ x, ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖ ≤
      g * (InfBound_A d l W τ' x + (if x = 0 then InfBound_J d l W τ' else 0)) := by
    intro x
    rw [ValZ.sigR_eq Sig P.ψ W E hl hdet x]
    refine InfBound_expVal_le _ _ _ fun g' hg' => ?_
    have h := hW₂ W (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW) g' hg'
      (Sinf P.ψ W) hs E hE 0 x
    have hA : InfBound_A d l W τ' (0 - x) = InfBound_A d l W τ' x := by
      simp only [InfBound_A, zero_sub, zdInf_neg]
    have hJ : (if (0 : Fin d → ℤ) = x then InfBound_J d l W τ' else 0) =
        (if x = 0 then InfBound_J d l W τ' else 0) := by
      by_cases hx : x = 0
      · subst hx
        rfl
      · rw [ite_eq_right (Ne.symm hx), ite_eq_right hx]
    rwa [hA, hJ] at h
  obtain ⟨hA1, hA2⟩ := InfBound_A_sum (d := d) (l := l) hW1 (hL W hW1)
  have hIs : HasSum (fun x : Fin d → ℤ => if x = 0 then InfBound_J d l W τ' else 0)
      (InfBound_J d l W τ') := hasSum_ite_eq 0 _
  have hFs : Summable (fun x => g * (InfBound_A d l W τ' x +
      (if x = 0 then InfBound_J d l W τ' else 0))) := (hA1.add hIs.summable).mul_left g
  have hRs : Summable (fun x => ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖) :=
    Summable.of_nonneg_of_le (fun x => norm_nonneg _) hpt hFs
  have hRt : ∑' x, ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖ ≤
      g * (CL + 1) * InfBound_J d l W τ' := by
    calc ∑' x, ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖
        ≤ ∑' x, g * (InfBound_A d l W τ' x + (if x = 0 then InfBound_J d l W τ' else 0)) :=
          hRs.tsum_le_tsum hpt hFs
      _ = g * (∑' x, InfBound_A d l W τ' x + InfBound_J d l W τ') := by
          rw [tsum_mul_left, hA1.tsum_add hIs.summable, hIs.tsum_eq]
      _ ≤ g * (CL * InfBound_J d l W τ' + InfBound_J d l W τ') := by gcongr
      _ = g * (CL + 1) * InfBound_J d l W τ' := by ring
  have hsum1 : ∑' y, Sinf P.ψ W y = 1 := hs.sum_one
  have hssum : Summable (Sinf P.ψ W) := by
    by_contra h
    rw [tsum_eq_zero_of_not_summable h] at hsum1
    norm_num at hsum1
  set R := ∑' y, ValZ.sigR Sig (Sinf P.ψ W) W E l y with hRdef
  have hRn : ‖R‖ ≤ g * (CL + 1) * InfBound_J d l W τ' :=
    (norm_tsum_le_tsum_norm hRs).trans hRt
  have hkpt : ∀ x, ‖ValZ.sigKer Sig P.ψ E l W x‖ ≤
      ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖ + ‖R‖ * |Sinf P.ψ W x| := by
    intro x
    rw [ValZ.sigKer_of_tsum Sig P.ψ E l W hsum1 x]
    calc ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x - R * (Sinf P.ψ W x : ℂ)‖
        ≤ ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖ + ‖R * (Sinf P.ψ W x : ℂ)‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine ⟨fun x => (hpt x).trans (InfBound_absorb hW1 (le_trans (hgc₁.trans hc₁T) hTW)
      hτ'.le hτ'2 x), hRs, ?_, fun x => ?_,
    Summable.of_nonneg_of_le (fun x => norm_nonneg _) hkpt
      (hRs.add ((summable_abs_iff.2 hssum).mul_left ‖R‖))⟩
  · calc ∑' x, ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖ ≤ g * (CL + 1) * InfBound_J d l W τ' := hRt
      _ ≤ (W : ℝ) ^ τ' * InfBound_J d l W τ' :=
          mul_le_mul_of_nonneg_right (hgCT.trans hTW) (InfBound_J_nonneg _ _ _)
      _ = InfBound_J d l W τ' * (W : ℝ) ^ τ' := mul_comm _ _
      _ ≤ InfBound_J d l W τ := InfBound_J_mul_le hW1 hτ'2
  · have hB0 : 0 ≤ (W : ℝ) ^ (-(d : ℝ)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
        ((zdInf x : ℝ) + W) ^ (-(2 * (d : ℝ) - 4)) := by
      have := InfBound_br_pos hW1 x
      positivity
    calc ‖ValZ.sigKer Sig P.ψ E l W x‖
        ≤ ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖ + ‖R‖ * |Sinf P.ψ W x| := hkpt x
      _ ≤ g * (InfBound_A d l W τ' x + (if x = 0 then InfBound_J d l W τ' else 0)) +
          g * (CL + 1) * InfBound_J d l W τ' * (Ck * ((W : ℝ) ^ (-(d : ℝ)) *
            (W : ℝ) ^ (2 * (d : ℝ) - 4) * ((zdInf x : ℝ) + W) ^ (-(2 * (d : ℝ) - 4)))) :=
          add_le_add (hpt x) (mul_le_mul hRn (InfBound_decay hs hW1 (by omega) x)
            (abs_nonneg _) (mul_nonneg (by positivity) (InfBound_J_nonneg _ _ _)))
      _ = g * (InfBound_A d l W τ' x + (if x = 0 then InfBound_J d l W τ' else 0)) +
          g * (CL + 1) * Ck * (InfBound_J d l W τ' * ((W : ℝ) ^ (-(d : ℝ)) *
            (W : ℝ) ^ (2 * (d : ℝ) - 4) * ((zdInf x : ℝ) + W) ^ (-(2 * (d : ℝ) - 4)))) := by
          ring
      _ ≤ g * (InfBound_A d l W τ' x + (if x = 0 then InfBound_J d l W τ' else 0)) +
          g * (CL + 1) * Ck * InfBound_A d l W τ' x := by
          gcongr
          exact InfBound_J_mul_B_le hW1 hτ'.le x
      _ = c₁ * (InfBound_A d l W τ' x + (if x = 0 then InfBound_J d l W τ' else 0)) -
          g * (CL + 1) * Ck * (if x = 0 then InfBound_J d l W τ' else 0) := by
          rw [hc₁def]
          ring
      _ ≤ c₁ * (InfBound_A d l W τ' x + (if x = 0 then InfBound_J d l W τ' else 0)) :=
          sub_le_self _ (mul_nonneg (by positivity) (hI0 x))
      _ ≤ InfBound_A d l W τ x + (if x = 0 then InfBound_J d l W τ else 0) :=
          InfBound_absorb hW1 (hc₁T.trans hTW) hτ'.le hτ'2 x

/-- `ValZ.SelUnif` at a lower order. -/
private theorem InfBound_selUnif_mono {κ : ℝ} {M N : ℕ} {K : ℝ → KerInf d}
    (h : ValZ.SelUnif κ N K) (hMN : M ≤ N) : ValZ.SelUnif κ M K :=
  fun Esel hsel l h4 hl he => h Esel hsel l h4 (hl.trans hMN) he

/-- **[I, (2.13), (2.14), (2.16)] for the label kernels `Σ̊^∞_l`** ([I, Def 8.2] on `ℤ^d`, with
the diagonal term of `KerInfHyp`): for `d ≥ 6`, a profile `P`, a family `Sig` whose even orders
`4 ≤ k ≤ N` have the shape of a `k`-th order self-energy and `κ > 0`, the kernels
`Σ̊^∞_l = ValZ.sigKer Sig P.ψ` at `S_∞ = Sinf P.ψ W` satisfy `KerInfHyp` at every even
`l ∈ [4, N]` along every choice of energies `|E(W)| < 2 − κ`. By induction on the order:
`Σ^{(r),∞}_l` reads `Σ̊^∞` below `l` (`ValZ.sigR_eq`), [I, (8.7)] holds for it, and
`Σ̊^∞_l = Σ^{(r),∞}_l − [Σ_y Σ^{(r),∞}_l(0, y)] S_∞` with
`|S_∞(x)| ≲ W^{-d} (1 + |x|/W)^{-(2d-4)}`. -/
theorem InfBound.selUnif (hd : 6 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergyShapesUpTo Sig N) {κ : ℝ} (hκ : 0 < κ) :
    ValZ.SelUnif κ N (ValZ.sigKer Sig P.ψ) := by
  suffices h : ∀ M, M ≤ N → ValZ.SelUnif κ M (ValZ.sigKer Sig P.ψ) from h N le_rfl
  intro M
  induction M with
  | zero => intro _ Esel _ l hl4 hl0 _; omega
  | succ M ih =>
    intro hM Esel hsel l hl4 hlM hle
    by_cases hlt : l ≤ M
    · exact ih (by omega) Esel hsel l hl4 hlt hle
    · have hl : l = M + 1 := by omega
      have hK : ValZ.SelUnif κ (l - 1) (ValZ.sigKer Sig P.ψ) := by
        rw [hl, Nat.add_sub_cancel]
        exact ih (by omega)
      refine ⟨fun W a => ValZ.sigKer_neg Sig P.ψ (Esel W) l W a, fun τ hτ => ?_,
        fun W => ValZ.tsum_sigKer Sig P.ψ (Esel W) l W⟩
      obtain ⟨W₀, hW₀⟩ := InfBound_level hd P Sig (by omega) (hSig l hl4 (by omega) hle) hκ hK
        τ hτ
      exact ⟨W₀, fun W hW x => (hW₀ W hW (Esel W) (hsel W)).2.2.2.1 x⟩

/-- **[I, Lemma 8.4, (8.7)] for `Σ^{(r),∞}_l`**, with the diagonal term: for `d ≥ 6`, a profile
`P`, a family `Sig` whose even orders `4 ≤ k ≤ N` have the shape of a `k`-th order self-energy and
`κ > 0`: for every even `l ∈ [4, N]` and `τ > 0` there is `W₀` such that for `W ≥ W₀`,
`|E| < 2 − κ` and `x ∈ ℤ^d`,
`|Σ^{(r),∞}_l(0, x)| ≤ W^{-ld/2} W^{2d-4} ⟨x⟩^{-(2d-4-τ)} + 1_{x=0} W^{-(l-2)d/2} W^τ`,
`x ↦ |Σ^{(r),∞}_l(0, x)|` is summable and `Σ_x |Σ^{(r),∞}_l(0, x)| ≤ W^{-(l-2)d/2} W^τ`. -/
theorem InfBound.sigRBound (hd : 6 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergyShapesUpTo Sig N) {κ : ℝ} (hκ : 0 < κ) :
    ∀ l, 4 ≤ l → l ≤ N → Even l → ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W →
      ∀ E : ℝ, |E| < 2 - κ →
        (∀ x : Fin d → ℤ, ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖ ≤
          (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
            ((zdInf x : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - τ)) +
          (if x = 0 then (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ τ else 0)) ∧
        Summable (fun x : Fin d → ℤ => ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖) ∧
        ∑' x : Fin d → ℤ, ‖ValZ.sigR Sig (Sinf P.ψ W) W E l x‖ ≤
          (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ τ := by
  intro l hl4 hlN hle τ hτ
  obtain ⟨W₀, h⟩ := InfBound_level hd P Sig (by omega) (hSig l hl4 hlN hle) hκ
    (InfBound_selUnif_mono (InfBound.selUnif hd P Sig N hSig hκ) (by omega)) τ hτ
  exact ⟨W₀, fun W hW E hE => ⟨(h W hW E hE).1, (h W hW E hE).2.1, (h W hW E hE).2.2.1⟩⟩

/-- **[I, (8.7)] for the label kernels `Σ̊^∞_l`**, with the diagonal term, under the hypotheses of
`InfBound.sigRBound`: for every even `l ∈ [4, N]` and `τ > 0` there is `W₀` such that for
`W ≥ W₀`, `|E| < 2 − κ` and `x ∈ ℤ^d`,
`|Σ̊^∞_l(0, x)| ≤ W^{-ld/2} W^{2d-4} ⟨x⟩^{-(2d-4-τ)} + 1_{x=0} W^{-(l-2)d/2} W^τ`, and
`x ↦ |Σ̊^∞_l(0, x)|` is summable. -/
theorem InfBound.sigKerBound (hd : 6 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergyShapesUpTo Sig N) {κ : ℝ} (hκ : 0 < κ) :
    ∀ l, 4 ≤ l → l ≤ N → Even l → ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W →
      ∀ E : ℝ, |E| < 2 - κ →
        (∀ x : Fin d → ℤ, ‖ValZ.sigKer Sig P.ψ E l W x‖ ≤
          (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
            ((zdInf x : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - τ)) +
          (if x = 0 then (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ τ else 0)) ∧
        Summable (fun x : Fin d → ℤ => ‖ValZ.sigKer Sig P.ψ E l W x‖) := by
  intro l hl4 hlN hle τ hτ
  obtain ⟨W₀, h⟩ := InfBound_level hd P Sig (by omega) (hSig l hl4 hlN hle) hκ
    (InfBound_selUnif_mono (InfBound.selUnif hd P Sig N hSig hκ) (by omega)) τ hτ
  exact ⟨W₀, fun W hW E hE => ⟨(h W hW E hE).2.2.2.1, (h W hW E hE).2.2.2.2⟩⟩


/-! ## The symbol of `Σ̊^∞_l` -/

/-- `|x_i| ≤ |x|_∞`. -/
private theorem InfBound_abs_le_zdInf (x : Fin d → ℤ) (i : Fin d) :
    |((x i : ℤ) : ℝ)| ≤ (zdInf x : ℝ) := by
  have h := Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)
  have h' : (((x i).natAbs : ℕ) : ℝ) ≤ (zdInf x : ℝ) := by exact_mod_cast h
  rwa [Nat.cast_natAbs, Int.cast_abs] at h'

/-- `|p·x| ≤ d ‖p‖ |x|_∞`, with `‖p‖` the sup norm. -/
private theorem InfBound_dot_le (p : Fin d → ℝ) (x : Fin d → ℤ) :
    |∑ i, p i * (x i : ℝ)| ≤ d * ‖p‖ * (zdInf x : ℝ) := by
  calc |∑ i, p i * (x i : ℝ)| ≤ ∑ i, |p i * (x i : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖p‖ * (zdInf x : ℝ) := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using norm_le_pi_norm p i)
          (InfBound_abs_le_zdInf x i) (abs_nonneg _) (norm_nonneg _)
    _ = d * ‖p‖ * (zdInf x : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- `e^{ip·x} + e^{−ip·x} − 2 = 2 (cos(p·x) − 1)`. -/
private theorem InfBound_zexp_add_neg (p : Fin d → ℝ) (x : Fin d → ℤ) :
    zexp p x + zexp p (-x) - 2 = ((2 * (Real.cos (∑ i, p i * (x i : ℝ)) - 1) : ℝ) : ℂ) := by
  have h : (∑ i, p i * (((-x) i : ℤ) : ℝ)) = -(∑ i, p i * (x i : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  unfold zexp
  rw [h]
  set θ := ∑ i, p i * (x i : ℝ)
  rw [Complex.ofReal_neg, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

/-- `|2 (cos θ − 1)| ≤ θ²`. -/
private theorem InfBound_norm_cos_le (θ : ℝ) : ‖((2 * (Real.cos θ - 1) : ℝ) : ℂ)‖ ≤ θ ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by nlinarith [Real.cos_le_one θ])]
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := θ)]

/-- **The symbol of `Σ̊^∞_l`** ([I, Def 8.2], text after (8.3), in the exact form): for `d ≥ 8`,
a profile `P`, a family `Sig` whose even orders `4 ≤ k ≤ N` have the shape of a `k`-th order
self-energy and `κ > 0`: for every even `l ∈ [4, N]` and `τ > 0` there are `C ≥ 0` and `W₀` such
that for `W ≥ W₀`, `|E| < 2 − κ` and `p ∈ [−π, π]^d`,
`|ψ_{Σ̊^∞_l}(p)| ≤ C W^τ W^{-(l-2)d/2} W² ‖p‖²`, where `ψ_{Σ̊^∞_l}(p) = Σ_x Σ̊^∞_l(0, x) e^{ip·x}`
(`zdSeries`) and `‖p‖ = max_i |p_i|`. The row sum of `Σ̊^∞_l` is `0` (`ValZ.tsum_sigKer`) and
`Σ̊^∞_l` is even (`ValZ.sigKer_neg`), so `ψ_{Σ̊^∞_l}(p) = Σ_x Σ̊^∞_l(0, x) (cos(p·x) − 1)`; the
term `x = 0` vanishes, and `Σ_x |x|² W^{-ld/2} W^{2d-4} ⟨x⟩^{-(2d-4-τ)} ≲ W^{-(l-2)d/2} W^{2+τ}`
for `d > 6 + τ` (`InfBound.sigKerBound`). -/
theorem InfBound.symbolBound (hd : 8 ≤ d) (P : Profile d) (Sig : ℕ → Expansion 2) (N : ℕ)
    (hSig : SelfEnergyShapesUpTo Sig N) {κ : ℝ} (hκ : 0 < κ) :
    ∀ l, 4 ≤ l → l ≤ N → Even l → ∀ τ : ℝ, 0 < τ → ∃ C W₀ : ℝ, 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E : ℝ, |E| < 2 - κ → ∀ p ∈ cubePi d,
        ‖zdSeries (ValZ.sigKer Sig P.ψ E l W) p‖ ≤
          C * (W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ 2 * ‖p‖ ^ 2 := by
  intro l hl4 hlN hle τ hτ
  set τ₁ := min τ 1 with hτ₁def
  have hτ₁ : 0 < τ₁ := lt_min hτ one_pos
  have hτ₁1 : τ₁ ≤ 1 := min_le_right _ _
  have hτ₁τ : τ₁ ≤ τ := min_le_left _ _
  obtain ⟨W₁, hW₁⟩ := InfBound.sigKerBound (by omega) P Sig N hSig hκ l hl4 hlN hle τ₁ hτ₁
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨CL, hCL, hL⟩ := latSum d (2 * d - 6 - τ₁) (by linarith)
  refine ⟨(d : ℝ) ^ 2 * CL / 2, max W₁ 1, by positivity, fun W hW E hE p _ => ?_⟩
  have hW1' : (1 : ℝ) ≤ W := le_trans (le_max_right _ _) hW
  have hW1 : 1 ≤ W := by exact_mod_cast hW1'
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨hK, hKs⟩ := hW₁ W (le_trans (le_max_left _ _) hW) E hE
  set K := ValZ.sigKer Sig P.ψ E l W with hKdef
  have hKneg : ∀ x, K (-x) = K x := fun x => ValZ.sigKer_neg Sig P.ψ E l W x
  have h0 : ∑' x, K x = 0 := ValZ.tsum_sigKer Sig P.ψ E l W
  have hK1 : Summable K := hKs.of_norm
  have hz1 : Summable (fun x => K x * zexp p x) := by
    refine Summable.of_norm ?_
    simpa only [norm_mul, norm_zexp, mul_one] using hKs
  have hz2 : Summable (fun x => K x * zexp p (-x)) := by
    refine Summable.of_norm ?_
    simpa only [norm_mul, norm_zexp, mul_one] using hKs
  have hf1 : Summable (fun x => K x * (zexp p x - 1)) := by
    have := hz1.sub hK1
    refine this.congr fun x => ?_
    ring
  have hf2 : Summable (fun x => K x * (zexp p (-x) - 1)) := by
    have := hz2.sub hK1
    refine this.congr fun x => ?_
    ring
  have e1 : zdSeries K p = ∑' x, K x * (zexp p x - 1) := by
    unfold zdSeries
    have : (fun x => K x * (zexp p x - 1)) = fun x => K x * zexp p x - K x := by
      funext x
      ring
    rw [this, hz1.tsum_sub hK1, h0, sub_zero]
  have e2 : zdSeries K p = ∑' x, K x * (zexp p (-x) - 1) := by
    rw [e1, ← (Equiv.neg (Fin d → ℤ)).tsum_eq]
    refine tsum_congr fun x => ?_
    simp only [Equiv.neg_apply, hKneg]
  have e3 : 2 * zdSeries K p = ∑' x, K x * (zexp p x + zexp p (-x) - 2) := by
    rw [two_mul]
    nth_rewrite 1 [e1]
    rw [e2, ← hf1.tsum_add hf2]
    refine tsum_congr fun x => ?_
    ring
  set m : (Fin d → ℤ) → ℝ := fun x => ((d : ℝ) * ‖p‖) ^ 2 * ((W : ℝ) ^ (-((l : ℝ) * d / 2)) *
    (W : ℝ) ^ (2 * (d : ℝ) - 4) * ((zdInf x : ℝ) + W) ^ (-(2 * (d : ℝ) - 6 - τ₁))) with hmdef
  obtain ⟨hLs, hLt⟩ := hL W hW1
  have hms : Summable m := hLs.mul_left _ |>.mul_left _
  have hmt : ∑' x, m x ≤ ((d : ℝ) * ‖p‖) ^ 2 * (CL * ((W : ℝ) ^ τ₁ *
      (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ 2)) := by
    rw [hmdef, tsum_mul_left, tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
          ∑' x : Fin d → ℤ, ((zdInf x : ℝ) + W) ^ (-(2 * (d : ℝ) - 6 - τ₁))
        ≤ (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
          (CL * (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 6 - τ₁))) :=
          mul_le_mul_of_nonneg_left hLt (by positivity)
      _ = CL * ((W : ℝ) ^ τ₁ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ 2) := by
          have hexp : (W : ℝ) ^ (-((l : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
              (W : ℝ) ^ ((d : ℝ) - (2 * (d : ℝ) - 6 - τ₁)) =
              (W : ℝ) ^ τ₁ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ 2 := by
            rw [← Real.rpow_natCast (W : ℝ) 2, ← Real.rpow_add hW0, ← Real.rpow_add hW0,
              ← Real.rpow_add hW0, ← Real.rpow_add hW0]
            congr 1
            push_cast
            ring
          rw [← hexp]
          ring
  have hpt : ∀ x, ‖K x * (zexp p x + zexp p (-x) - 2)‖ ≤ m x := by
    intro x
    rw [norm_mul, InfBound_zexp_add_neg]
    have hc := InfBound_norm_cos_le (∑ i, p i * (x i : ℝ))
    by_cases hx : x = 0
    · subst hx
      have : (∑ i, p i * (((0 : Fin d → ℤ) i : ℤ) : ℝ)) = 0 := by simp
      rw [this] at hc ⊢
      have hm0 : 0 ≤ m 0 := by
        have := InfBound_br_pos hW1 (0 : Fin d → ℤ)
        rw [hmdef]
        positivity
      calc ‖K 0‖ * ‖((2 * (Real.cos 0 - 1) : ℝ) : ℂ)‖ = 0 := by simp
        _ ≤ m 0 := hm0
    · have hKx : ‖K x‖ ≤ InfBound_A d l W τ₁ x := by
        have := hK x
        rwa [ite_eq_right hx, add_zero] at this
      have hb := InfBound_br_pos hW1 x
      have hθ : (∑ i, p i * (x i : ℝ)) ^ 2 ≤ ((d : ℝ) * ‖p‖) ^ 2 * ((zdInf x : ℝ) + W) ^ 2 := by
        have h1 := InfBound_dot_le p x
        have h2 : (d : ℝ) * ‖p‖ * (zdInf x : ℝ) ≤ (d : ℝ) * ‖p‖ * ((zdInf x : ℝ) + W) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        rw [← mul_pow, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
      calc ‖K x‖ * ‖((2 * (Real.cos (∑ i, p i * (x i : ℝ)) - 1) : ℝ) : ℂ)‖
          ≤ InfBound_A d l W τ₁ x * (((d : ℝ) * ‖p‖) ^ 2 * ((zdInf x : ℝ) + W) ^ 2) :=
            mul_le_mul hKx (hc.trans hθ) (norm_nonneg _) (InfBound_A_nonneg hW1 _ _)
        _ = m x := by
            simp only [hmdef, InfBound_A]
            rw [← Real.rpow_natCast ((zdInf x : ℝ) + W) 2]
            have : ((zdInf x : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - τ₁)) *
                ((zdInf x : ℝ) + W) ^ ((2 : ℕ) : ℝ) =
                ((zdInf x : ℝ) + W) ^ (-(2 * (d : ℝ) - 6 - τ₁)) := by
              rw [← Real.rpow_add hb]
              congr 1
              push_cast
              ring
            rw [← this]
            ring
  have h2 : ‖2 * zdSeries K p‖ ≤ ∑' x, m x := by
    rw [e3]
    exact tsum_of_norm_bounded hms.hasSum hpt
  rw [norm_mul, Complex.norm_two] at h2
  have hWτ : (W : ℝ) ^ τ₁ ≤ (W : ℝ) ^ τ := Real.rpow_le_rpow_of_exponent_le hW1' hτ₁τ
  calc ‖zdSeries K p‖ ≤ (((d : ℝ) * ‖p‖) ^ 2 * (CL * ((W : ℝ) ^ τ₁ *
        (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ 2))) / 2 := by
        linarith [h2.trans hmt]
    _ ≤ (((d : ℝ) * ‖p‖) ^ 2 * (CL * ((W : ℝ) ^ τ *
        (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) * (W : ℝ) ^ 2))) / 2 := by
        gcongr
    _ = (d : ℝ) ^ 2 * CL / 2 * (W : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) *
          (W : ℝ) ^ 2 * ‖p‖ ^ 2 := by ring


section Instances

end Instances

end RBM8D
