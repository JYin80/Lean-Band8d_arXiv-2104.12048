import RBM8D.SelfEnergy.ContractShape
import RBM8D.SelfEnergy.Step
import RBM8D.Bound.DoublyDet
import RBM8D.Bound.ChainInf
import RBM8D.Bound.AuxTreeZ
import RBM8D.Kernel.ShellKernel
import RBM8D.Kernel.Sinf
import RBM8D.Profile.Density
import Batteries.Tactic.OpenPrivate

/-!
# Values of deterministic graphs on `ℤ^d` ([I, Def 7.1, Cor 7.6, Def 8.2])

On `ℤ^d` a kernel is a function of the offset: the factor of a component with ends labelled
`a, b ∈ ℤ^d` is read at `b − a`.

* `ValZ.Rec`, `ValZ.rec`: the data of [I, Def 7.1 (1)–(4)]: `m = m(E)`, `S_∞` ([I, (7.3)]),
  `S^±_∞(m)` ([I, (7.4)]) and the chains `Θ_∞ Σ^∞_{o₁} Θ_∞ ⋯ Σ^∞_{o_l} Θ_∞` of the labelled
  `Θ_∞` edges ([I, (7.5)], [I, Def 7.1 (3)]); a dotted edge is `1_{a = b}` and a `×`-dotted edge
  `1_{a ≠ b}`.
* `ValZ.val`, `ValZ.absVal`: the value `Σ_{σ ∈ (ℤ^d)^n}` of the term of a graph and of its
  absolute value ([I, Def 7.1 (5)]), as sums in `ℂ` and `ℝ` with the convention of `tsum`.
* `ValZ.val_neg`: invariance under `x ↦ −x` when every kernel of the record is even; `ValZ.rec_even`: the record at an even kernel `s` and
  even label kernels is even, at every `W` (evenness of [I, (8.6)]).
* `G13.dotContract'`: the contraction of the dotted edges between an internal and an external
  atom ([I, Def 3.1]) keeps the value and the absolute value on `ℤ^d` as well.
* `ValZ.corBound`: [I, Cor 7.6] = [I, (8.7)] on `ℤ^d`: for `d ≥ 6` and a deterministic graph whose
  internal form is normal regular and doubly connected, the summand of the absolute value is
  summable and `|Γ^∞|^{abs}_{xy} ≤ W^{-n_Γ d/2} W^{2d-4} ⟨x − y⟩^{-(2d-4-τ)}`, with `W₀` uniform in
  `|E| < 2 − κ` when the label kernels satisfy [I, (2.13), (2.14), (2.16)] along every choice of
  energies `E(W)` (`ValZ.SelUnif`). The proof reduces the graph to two spanning trees
  ([I, Def 6.5]) and uses [I, Claim 6.11] on `ℤ^d`.
* `ValZ.renorm`, `ValZ.sigUpTo`, `ValZ.sigR`, `ValZ.sigRing`, `ValZ.sigKer`, `ValZ.rowSum`:
  [I, Def 8.2] on `ℤ^d`: `Σ^{(r),∞}_l` reads `Σ̊^∞` at the lower orders, and
  `Σ̊^∞_l = Σ^{(r),∞}_l − [Σ_x Σ^{(r),∞}_l(0, x)] S_∞`; where `Σ_x S_∞(x) ≠ 1` the subtraction uses
  `δ_0` in place of `S_∞`. `ValZ.sigKer_neg` and `ValZ.tsum_sigKer`: `Σ̊^∞_l` is even and has
  row sum `0` at every `W`. `ValZ.rowSum` is the number `R(E, W) = Σ_{x ∈ ℤ^d} Σ^{(r),∞}_n(0, x)`
  of [I, (8.8)].
-/

noncomputable section

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace RBM8D

open Graphs

open private dc_trees tree_length no_dot ord_eq_sum const_le_rpow from RBM8D.Bound.DoublyDet
open private Contract_elim_insertNth from RBM8D.SelfEnergy.Contract
open private ContractShape_ends from RBM8D.SelfEnergy.ContractShape

variable {d : ℕ}

/-! ## The data and the value on `ℤ^d` -/

/-- A data record on `ℤ^d` ([I, Def 7.1]): `m`, and the kernels of the waved edges `s`, `S⁺`,
`S⁻` and of the `Θ` edges with label `o`, as functions of the offset. -/
structure ValZ.Rec (d : ℕ) where
  m : ℂ
  S : (Fin d → ℤ) → ℂ
  Sp : (Fin d → ℤ) → ℂ
  Sm : (Fin d → ℤ) → ℂ
  chain : List ℕ → (Fin d → ℤ) → ℂ

/-- The record of [I, Def 7.1 (1)–(4)] at the kernel `s`, the label kernels `K`, the band width
`W` and the energy `E`: `m = m(E)`, `S = s`, `S^± = S^±_∞(m(E))` and the chain
`Θ_∞ Σ^∞_{o₁} Θ_∞ ⋯ Σ^∞_{o_l} Θ_∞` with `Σ^∞_{oᵢ} = K oᵢ W`. -/
def ValZ.rec (s : (Fin d → ℤ) → ℝ) (K : KerInf d) (W : ℕ) (E : ℝ) : ValZ.Rec d where
  m := mE E
  S := fun x => (s x : ℂ)
  Sp := SplusInf (mE E) s
  Sm := SminusInf (mE E) s
  chain := chainZ s K W

/-- The factor of one component at the labelling `σ` of the atoms by points of `ℤ^d`: the
kernel of its kind at `σ y − σ x`, `1_{σ x = σ y}` for a dotted and `1_{σ x ≠ σ y}` for a
`×`-dotted edge, and `0` for the kinds that a deterministic graph does not contain. -/
def ValZ.compVal {V : Type*} (D : ValZ.Rec d) (σ : V → Fin d → ℤ) (c : Comp V) : ℂ :=
  match c.kind with
  | .waved .s => D.S (σ c.y - σ c.x)
  | .waved .plus => D.Sp (σ c.y - σ c.x)
  | .waved .minus => D.Sm (σ c.y - σ c.x)
  | .theta o => D.chain o (σ c.y - σ c.x)
  | .dot => if σ c.x = σ c.y then 1 else 0
  | .xdot => if σ c.x = σ c.y then 0 else 1
  | _ => 0

/-- The product of the coefficient at `m` and of all component factors at the labelling `σ`. -/
def ValZ.term {k n : ℕ} (Γ : Graph k n) (D : ValZ.Rec d) (σ : Atom k n → Fin d → ℤ) : ℂ :=
  Γ.coeff.eval D.m * (Γ.comps.map (ValZ.compVal D σ)).prod

/-- The value of a graph on `ℤ^d` ([I, Def 7.1 (5)]): the sum over the labels `s ∈ (ℤ^d)^n` of
the internal atoms of `ValZ.term`, the external atoms being labelled by `e`. -/
def ValZ.val {k n : ℕ} (Γ : Graph k n) (D : ValZ.Rec d) (e : Fin k → Fin d → ℤ) : ℂ :=
  ∑' s : Fin n → Fin d → ℤ, ValZ.term Γ D (Sum.elim e s)

/-- The value of the absolute-value graph on `ℤ^d`: every factor and the coefficient replaced by
its absolute value. -/
def ValZ.absVal {k n : ℕ} (Γ : Graph k n) (D : ValZ.Rec d) (e : Fin k → Fin d → ℤ) : ℝ :=
  ∑' s : Fin n → Fin d → ℤ, ‖ValZ.term Γ D (Sum.elim e s)‖

/-- The value on `ℤ^d` of a formal sum of graphs: the sum of the values of its terms. -/
def ValZ.expVal {k : ℕ} (E : Expansion k) (D : ValZ.Rec d) (e : Fin k → Fin d → ℤ) : ℂ :=
  (E.map fun g => ValZ.val g.2 D e).sum

/-- `|Γ^∞_{xy}| ≤ |Γ^∞|^{abs}_{xy}` when the summand of the absolute value is summable. -/
theorem ValZ.norm_val_le {k n : ℕ} (Γ : Graph k n) (D : ValZ.Rec d) (e : Fin k → Fin d → ℤ)
    (h : Summable fun s : Fin n → Fin d → ℤ => ‖ValZ.term Γ D (Sum.elim e s)‖) :
    ‖ValZ.val Γ D e‖ ≤ ValZ.absVal Γ D e :=
  norm_tsum_le_tsum_norm h

/-! ## Translation and reflection -/

/-- A record whose kernels are all even. -/
def ValZ.Rec.Even (D : ValZ.Rec d) : Prop :=
  (∀ x, D.S (-x) = D.S x) ∧ (∀ x, D.Sp (-x) = D.Sp x) ∧ (∀ x, D.Sm (-x) = D.Sm x) ∧
    ∀ o x, D.chain o (-x) = D.chain o x

/-- A component factor is invariant under `σ ↦ −σ` for an even record. -/
private theorem ValZ_compVal_neg {V : Type*} {D : ValZ.Rec d} (hD : D.Even)
    (σ : V → Fin d → ℤ) : ValZ.compVal D (fun u => -σ u) = ValZ.compVal D σ := by
  funext c
  obtain ⟨hS, hSp, hSm, hch⟩ := hD
  have e : ∀ a b : Fin d → ℤ, -b - -a = -(b - a) := fun a b => by abel
  unfold ValZ.compVal
  rcases c with ⟨κ, x, y, mi, lab⟩
  cases κ with
  | waved w => cases w <;> simp only [e, hS, hSp, hSm]
  | theta o => simp only [e, hch]
  | dot => simp only [neg_inj]
  | xdot => simp only [neg_inj]
  | _ => rfl

/-- For an even record the value on `ℤ^d` is invariant under `x ↦ −x`:
`Γ^∞(−x, −y) = Γ^∞(x, y)`. -/
theorem ValZ.val_neg {k n : ℕ} (Γ : Graph k n) {D : ValZ.Rec d} (hD : D.Even)
    (e : Fin k → Fin d → ℤ) : ValZ.val Γ D (fun i => -e i) = ValZ.val Γ D e := by
  unfold ValZ.val
  rw [← (Equiv.neg (Fin n → Fin d → ℤ)).tsum_eq]
  refine tsum_congr fun s => ?_
  have h : Sum.elim (fun i => -e i) ((Equiv.neg (Fin n → Fin d → ℤ)) s) =
      fun u => -Sum.elim e s u := by
    funext u; rcases u with u | u <;> rfl
  rw [h]
  unfold ValZ.term
  rw [ValZ_compVal_neg hD]

/-! ## Even kernels -/

/-- `e^{i(-p)·(-x)} = e^{ip·x}`. -/
private theorem ValZ_zexp_neg_neg (p : Fin d → ℝ) (x : Fin d → ℤ) : zexp (-p) (-x) = zexp p x := by
  unfold zexp
  congr 3
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- `e^{i(-p)·x} = e^{ip·(-x)}`. -/
private theorem ValZ_zexp_neg_left (p : Fin d → ℝ) (x : Fin d → ℤ) : zexp (-p) x = zexp p (-x) := by
  unfold zexp
  congr 3
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- The symbol of an even kernel is even. -/
private theorem ValZ_zdSymbol_neg {s : (Fin d → ℤ) → ℝ} (hs : ∀ x, s (-x) = s x)
    (p : Fin d → ℝ) : zdSymbol s (-p) = zdSymbol s p := by
  unfold zdSymbol zdSeries
  rw [← (Equiv.neg (Fin d → ℤ)).tsum_eq]
  refine tsum_congr fun x => ?_
  simp only [Equiv.neg_apply, hs, ValZ_zexp_neg_neg]

/-- The kernel with an even symbol is even. -/
private theorem ValZ_latticeFourier_neg {F : (Fin d → ℝ) → ℂ} (hF : ∀ p, F (-p) = F p)
    (x : Fin d → ℤ) : latticeFourier F (-x) = latticeFourier F x := by
  unfold latticeFourier
  congr 1
  have hpre : (Neg.neg ⁻¹' cubePi d : Set (Fin d → ℝ)) = cubePi d := by
    ext p
    simp only [Set.mem_preimage, cubePi, Set.mem_univ_pi, Set.mem_Icc, Pi.neg_apply]
    constructor
    · intro h i
      have := h i
      constructor <;> linarith [this.1, this.2]
    · intro h i
      have := h i
      constructor <;> linarith [this.1, this.2]
  have h := (Measure.measurePreserving_neg (volume : Measure (Fin d → ℝ))).setIntegral_preimage_emb
    (MeasurableEquiv.neg (Fin d → ℝ)).measurableEmbedding (fun p => F p * zexp p (-x)) (cubePi d)
  rw [hpre] at h
  rw [← h]
  refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Icc) fun p _ => ?_
  simp only [hF, neg_neg, ValZ_zexp_neg_left]

/-- `zdKernel F s` is even for an even kernel `s`. -/
private theorem ValZ_zdKernel_neg (F : ℂ → ℂ) {s : (Fin d → ℤ) → ℝ} (hs : ∀ x, s (-x) = s x)
    (x : Fin d → ℤ) : zdKernel F s (-x) = zdKernel F s x := by
  unfold zdKernel
  exact ValZ_latticeFourier_neg (fun p => by rw [ValZ_zdSymbol_neg hs]) x

/-- The convolution of two even kernels on `ℤ^d` is even. -/
private theorem ValZ_convZ_neg {f g : (Fin d → ℤ) → ℂ} (hf : ∀ x, f (-x) = f x)
    (hg : ∀ x, g (-x) = g x) (x : Fin d → ℤ) : convZ f g (-x) = convZ f g x := by
  unfold convZ
  rw [← (Equiv.neg (Fin d → ℤ)).tsum_eq]
  refine tsum_congr fun α => ?_
  simp only [Equiv.neg_apply, hf]
  rw [← hg (x - α)]
  congr 2
  abel

/-- The chains `Θ_∞ Σ^∞_{o₁} Θ_∞ ⋯ Σ^∞_{o_l} Θ_∞` are even when `s` and the label kernels are. -/
private theorem ValZ_chainZ_neg {s : (Fin d → ℤ) → ℝ} (hs : ∀ x, s (-x) = s x) {K : KerInf d}
    (W : ℕ) (hK : ∀ l x, K l W (-x) = K l W x) (o : List ℕ) (x : Fin d → ℤ) :
    chainZ s K W o (-x) = chainZ s K W o x := by
  unfold chainZ
  have hT : ∀ y, ThetaInf s (-y) = ThetaInf s y := fun y => by
    unfold ThetaInf ThetaZd; exact ValZ_zdKernel_neg _ hs y
  suffices h : ∀ F : (Fin d → ℤ) → ℂ, (∀ y, F (-y) = F y) → ∀ y,
      o.foldl (fun F l => convZ (convZ F (K l W)) (ThetaInf s)) F (-y) =
        o.foldl (fun F l => convZ (convZ F (K l W)) (ThetaInf s)) F y from h _ hT x
  induction o with
  | nil => intro F hF y; exact hF y
  | cons l o ih =>
    intro F hF y
    simp only [List.foldl_cons]
    exact ih _ (fun z => ValZ_convZ_neg (ValZ_convZ_neg hF (hK l)) hT z) y

/-- `S_∞ = φ_W / Σ φ_W` of [I, (7.3)] is even at every `W`. -/
theorem ValZ.Sinf_neg (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) (W : ℕ) (x : Fin d → ℤ) :
    Sinf ψ W (-x) = Sinf ψ W x := by
  unfold Sinf phiW
  congr 3
  funext q
  congr 1
  rw [← Real.cos_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- At an even kernel `s` and label kernels that are even at `W`, the record of
[I, Def 7.1 (1)–(4)] is even, at every `m(E)`. -/
theorem ValZ.rec_even {s : (Fin d → ℤ) → ℝ} (hs : ∀ x, s (-x) = s x) {K : KerInf d} (W : ℕ)
    (hK : ∀ l x, K l W (-x) = K l W x) (E : ℝ) : (ValZ.rec s K W E).Even := by
  have hp : ∀ x, SplusInf (mE E) s (-x) = SplusInf (mE E) s x := fun x => by
    unfold SplusInf; exact ValZ_zdKernel_neg _ hs x
  refine ⟨fun x => by simp only [ValZ.rec, hs], hp, fun x => ?_,
    fun o x => ValZ_chainZ_neg hs W hK o x⟩
  simp only [ValZ.rec, SminusInf, hp]

/-! ## Contraction of dotted edges on `ℤ^d` -/

/-- The factor of a dotted edge between `inr j` and `inl a₀` is `1(σ(inr j) = σ(inl a₀))`. -/
private theorem ValZ_compVal_dot {k n : ℕ} (D : ValZ.Rec d) (σ : Atom k (n + 1) → Fin d → ℤ)
    (c : Comp (Atom k (n + 1))) (j : Fin (n + 1)) (a₀ : Fin k) (hk : c.kind = .dot)
    (hxy : c.x = .inr j ∧ c.y = .inl a₀ ∨ c.x = .inl a₀ ∧ c.y = .inr j) :
    ValZ.compVal D σ c = if σ (.inr j) = σ (.inl a₀) then 1 else 0 := by
  obtain ⟨κ, x, y, mi, lab⟩ := c
  simp only at hk hxy
  subst hk
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · simp only [ValZ.compVal, eq_comm]

/-- **Contraction on `ℤ^d`.** If the `i`-th component of `Γ` is a dotted edge between the
internal atom `j` and the external atom `a₀`, the contraction `Contract.graph Γ i j a₀` has the
value and the absolute value of `Γ` on every record on `ℤ^d`: the summand of `Γ` vanishes unless
`j` sits at `a₀`, and `t ↦ (t with a₀ inserted at j)` is injective onto that support, so no
summability is needed. -/
theorem ValZ.val_contract {k n : ℕ} (Γ : Graph k (n + 1)) (i : Fin Γ.comps.length)
    (j : Fin (n + 1)) (a₀ : Fin k) (hk : Γ.comps[i].kind = .dot)
    (hxy : Γ.comps[i].x = .inr j ∧ Γ.comps[i].y = .inl a₀ ∨
      Γ.comps[i].x = .inl a₀ ∧ Γ.comps[i].y = .inr j)
    (D : ValZ.Rec d) (e : Fin k → Fin d → ℤ) :
    ValZ.val (Contract.graph Γ i j a₀) D e = ValZ.val Γ D e ∧
      ValZ.absVal (Contract.graph Γ i j a₀) D e = ValZ.absVal Γ D e := by
  have hperm := Contract.comps_perm Γ i
  have hterm : ∀ s : Fin (n + 1) → Fin d → ℤ, ValZ.term Γ D (Sum.elim e s) =
      if s j = e a₀ then Γ.coeff.eval D.m *
        ((Γ.comps.eraseIdx i).map (ValZ.compVal D (Sum.elim e s))).prod else 0 := by
    intro s
    unfold ValZ.term
    rw [← (hperm.map (ValZ.compVal D (Sum.elim e s))).prod_eq, List.map_cons, List.prod_cons,
      ValZ_compVal_dot D _ _ j a₀ hk hxy]
    simp only [Sum.elim_inr, Sum.elim_inl]
    split_ifs with h <;> simp [h]
  set g : (Fin n → Fin d → ℤ) → Fin (n + 1) → Fin d → ℤ :=
    fun t => Fin.insertNth (α := fun _ => Fin d → ℤ) j (e a₀) t with hg
  have hginj : Function.Injective g := fun t t' h => by
    have := congrArg (Fin.removeNth j) h
    simpa [hg] using this
  have hsupp : ∀ s : Fin (n + 1) → Fin d → ℤ, ValZ.term Γ D (Sum.elim e s) ≠ 0 →
      s ∈ Set.range g := by
    intro s hs
    rw [hterm] at hs
    have hj : s j = e a₀ := by
      by_contra h; exact hs (by simp [h])
    refine ⟨Fin.removeNth j s, ?_⟩
    rw [hg, ← hj]
    exact Fin.insertNth_self_removeNth j s
  have hg' : ∀ t, ValZ.term Γ D (Sum.elim e (g t)) =
      ValZ.term (Contract.graph Γ i j a₀) D (Sum.elim e t) := by
    intro t
    have hj : g t j = e a₀ := by simp [hg]
    rw [hterm]
    simp only [hj, ↓reduceIte]
    rw [hg, Contract_elim_insertNth j a₀ e t]
    unfold ValZ.term
    simp only [Contract.graph, List.map_map]
    congr 2
  constructor
  · unfold ValZ.val
    rw [← hginj.tsum_eq (f := fun s => ValZ.term Γ D (Sum.elim e s))
      (fun s hs => hsupp s hs)]
    exact tsum_congr fun t => (hg' t).symm
  · unfold ValZ.absVal
    rw [← hginj.tsum_eq (f := fun s => ‖ValZ.term Γ D (Sum.elim e s)‖)
      (fun s hs => hsupp s (fun h => hs (by simp only [h, norm_zero])))]
    exact tsum_congr fun t => by rw [hg']

/-- Contraction of the dotted edges between an internal and an external atom ([I, Def 3.1]) with
the value on `ℤ^d`: a graph with the shape of an `l`-th order self-energy has a graph with the
same value on every finite data record and the same value and absolute value on every record on
`ℤ^d`, with the shape of an `l`-th order self-energy, that is normal regular with `x`, `y` read as
internal atoms, or diagonal. -/
def G13.dotContractStmt' : Prop :=
  ∀ (l n : ℕ) (Γ : Graph 2 n), SelfEnergyShape l [⟨n, Γ⟩] →
    ∃ (n' : ℕ) (Γ' : Graph 2 n'), SelfEnergyShape l [⟨n', Γ'⟩] ∧
      (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι) (e : Fin 2 → ι),
        Γ'.val D e = Γ.val D e) ∧
      (∀ (d : ℕ) (D : ValZ.Rec d) (e : Fin 2 → Fin d → ℤ),
        ValZ.val Γ' D e = ValZ.val Γ D e ∧ ValZ.absVal Γ' D e = ValZ.absVal Γ D e) ∧
      ((∃ C, Γ'.internalize.Normal C) ∨ G13.IsDiag Γ')

/-- **The contraction on `ℤ^d`** ([I, Def 3.1], [I, Def 2.12]): every dotted edge between an
internal and an external atom is contracted, one at a time (`ContractShape.step`,
`Contract.val_eq`, `ValZ.val_contract`); at the end every dotted edge joins `x` and `y`
(`ContractShape.final`). -/
theorem G13.dotContract' : G13.dotContractStmt' := by
  intro l n
  induction n with
  | zero =>
    intro Γ hΓ
    exact ⟨0, Γ, hΓ, fun _ _ _ _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩,
      ContractShape.final Γ hΓ (ContractShape_ends Γ hΓ fun ⟨_, _, _, j, _⟩ => j.elim0)⟩
  | succ m ih =>
    intro Γ hΓ
    by_cases hex : ∃ c ∈ Γ.comps, c.kind = .dot ∧ ∃ (j : Fin (m + 1)) (a₀ : Fin 2),
        (c.x = .inr j ∧ c.y = .inl a₀ ∨ c.x = .inl a₀ ∧ c.y = .inr j)
    · obtain ⟨c, hc, hk, j, a₀, hxy⟩ := hex
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
      obtain ⟨n', Γ', h1, h2, h3, h4⟩ :=
        ih (Contract.graph Γ ⟨i, hi⟩ j a₀) (ContractShape.step Γ ⟨i, hi⟩ j a₀ hk hxy hΓ)
      refine ⟨n', Γ', h1, fun ι _ _ D e =>
        (h2 ι D e).trans (Contract.val_eq Γ ⟨i, hi⟩ j a₀ hk hxy D e), fun d D e => ?_, h4⟩
      obtain ⟨h5, h6⟩ := ValZ.val_contract Γ ⟨i, hi⟩ j a₀ hk hxy D e
      exact ⟨(h3 d D e).1.trans h5, (h3 d D e).2.trans h6⟩
    · exact ⟨m + 1, Γ, hΓ, fun _ _ _ _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩,
        ContractShape.final Γ hΓ (ContractShape_ends Γ hΓ hex)⟩

/-! ## Uniformity in the energy -/

/-- A threshold uniform in `|E| < 2 − κ` from thresholds along every choice of energies
`E(W)`: choose at each `W` an energy that violates the property, if there is one. -/
private theorem ValZ_uniform {κ : ℝ} (P : ℝ → ℕ → Prop)
    (h : ∀ Esel : ℕ → ℝ, (∀ W, |Esel W| < 2 - κ) → ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → P (Esel W) W) :
    ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ E : ℝ, |E| < 2 - κ → P E W := by
  classical
  by_cases hκ : 0 < 2 - κ
  · let Esel : ℕ → ℝ := fun W => if hW : ∃ E, |E| < 2 - κ ∧ ¬ P E W then hW.choose else 0
    have hsel : ∀ W, |Esel W| < 2 - κ := by
      intro W
      simp only [Esel]
      split_ifs with hW
      · exact hW.choose_spec.1
      · simpa using hκ
    obtain ⟨W₀, hW₀⟩ := h Esel hsel
    refine ⟨W₀, fun W hW E hE => ?_⟩
    by_contra hP
    have hex : ∃ E, |E| < 2 - κ ∧ ¬ P E W := ⟨E, hE, hP⟩
    have h1 := hW₀ W hW
    simp only [Esel, hex, ↓reduceDIte] at h1
    exact hex.choose_spec.2 h1
  · exact ⟨0, fun W _ E hE => absurd (lt_of_le_of_lt (abs_nonneg E) hE) hκ⟩

/-- `|1 − m(E)²|² = 4 − E²` for `|E| ≤ 2`. -/
private theorem ValZ_norm_one_sub_sq {E : ℝ} (hE : |E| ≤ 2) :
    ‖1 - mE E ^ 2‖ ^ 2 = 4 - E ^ 2 := by
  have h4 : 0 ≤ 4 - E ^ 2 := by
    have := abs_le.mp hE
    nlinarith
  have ht := Real.sq_sqrt h4
  set t := Real.sqrt (4 - E ^ 2) with htdef
  have him : (mE E).im = t / 2 := mE_im E
  rw [Complex.sq_norm, Complex.normSq_apply, sq (mE E)]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re,
    Complex.mul_im, mE_re, him]
  linear_combination ((1 - E ^ 2 / 4) / 2 + (t ^ 2 + 4 - E ^ 2) / 16 + E ^ 2 / 4) * ht

/-- A coefficient is bounded at `m(E)` uniformly in `|E| < 2 − κ`. -/
private theorem ValZ_coeff_bound {κ : ℝ} (hκ : 0 < κ) (p : Coeff) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ E : ℝ, |E| < 2 - κ → ‖p.eval (mE E)‖ ≤ C := by
  set c : ℝ := Real.sqrt (4 - (2 - κ) ^ 2) with hcdef
  set R : ℝ := 1 + 1 / c with hRdef
  have hR : ∀ E : ℝ, |E| < 2 - κ → ∀ v, ‖CVar.eval (mE E) v‖ ≤ R := by
    intro E hE v
    have hκ2 : κ < 2 := by linarith [abs_nonneg E]
    have hE2 : |E| ≤ 2 := by linarith
    have hm := norm_mE hE2
    have hc : 0 < c := Real.sqrt_pos.2 (by nlinarith)
    have hc1 : 0 ≤ 1 / c := by positivity
    have hlow : c ≤ ‖1 - mE E ^ 2‖ := by
      rw [hcdef, ← Real.sqrt_sq (norm_nonneg (1 - mE E ^ 2)), ValZ_norm_one_sub_sq hE2]
      refine Real.sqrt_le_sqrt ?_
      have h1 : E ^ 2 ≤ (2 - κ) ^ 2 := by
        rw [← sq_abs E]
        exact pow_le_pow_left₀ (abs_nonneg E) hE.le 2
      linarith
    have hinv : ‖(1 - mE E ^ 2)⁻¹‖ ≤ 1 / c := by
      rw [norm_inv, one_div]
      exact inv_anti₀ hc hlow
    have hconj : (1 - star (mE E) ^ 2) = star (1 - mE E ^ 2) := by simp [star_sub, star_pow]
    cases v with
    | m => simp only [CVar.eval]; linarith
    | mInv => simp only [CVar.eval, norm_inv, hm]; linarith
    | r => simp only [CVar.eval]; linarith
    | mBar => simp only [CVar.eval, norm_star, hm]; linarith
    | mBarInv => simp only [CVar.eval, norm_inv, norm_star, hm]; linarith
    | rBar =>
      simp only [CVar.eval]
      rw [hconj, norm_inv, norm_star, ← norm_inv]
      linarith
  refine ⟨∑ s ∈ p.support, ‖p.coeff s‖ * ∏ i ∈ s.support, R ^ s i, ?_, fun E hE => ?_⟩
  · refine Finset.sum_nonneg fun s _ => mul_nonneg (norm_nonneg _) (Finset.prod_nonneg
      fun i _ => pow_nonneg (by positivity) _)
  · unfold Coeff.eval
    rw [MvPolynomial.eval_eq]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [norm_mul, norm_prod]
    gcongr with i
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hR E hE i) _

/-! ## The waved edges on `ℤ^d` -/

/-- The bound `K_w W^{τ} W^{d-4} ⟨z⟩^{-(2d-4)}` of the waved edges. -/
private def ValZ_wb (d W : ℕ) (Kw τc : ℝ) (z : Fin d → ℤ) : ℝ :=
  Kw * (W : ℝ) ^ τc * ((W : ℝ) ^ ((d : ℝ) - 4) * ((zdInf z : ℝ) + W) ^ (-(2 * (d : ℝ) - 4)))

/-- The waved edges `s`, `S^±_∞(m(E))` are at most `K_w W^{τ} W^{d-4} ⟨z⟩^{-(2d-4)}`, uniformly in
`|E| < 2 − κ` and `W ≥ W₀`: from the decay [I, (1.8)] of `s` and [I, (7.6)]. -/
private theorem ValZ_wave_bound (hd : 6 ≤ d) (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ)
    (c' : ℝ) (hψ : SymbolBound ψ c') (C : ℕ → ℝ) {κ : ℝ} (hκ : 0 < κ) {τc : ℝ} (hτc : 0 < τc) :
    ∃ Kw W₀ : ℝ, 0 ≤ Kw ∧ ∀ W : ℕ, W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ E : ℝ, |E| < 2 - κ → ∀ z : Fin d → ℤ,
        ‖((s z : ℝ) : ℂ)‖ ≤ ValZ_wb d W Kw τc z ∧ ‖SplusInf (mE E) s z‖ ≤ ValZ_wb d W Kw τc z ∧
          ‖SminusInf (mE E) s z‖ ≤ ValZ_wb d W Kw τc z := by
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  have hk : (0 : ℝ) < 2 * d - 4 := by linarith
  set τS : ℝ := τc / (2 * (d : ℝ) - 4) with hτSdef
  have hτS : 0 < τS := div_pos hτc hk
  have hτSk : τS * (2 * (d : ℝ) - 4) = τc := by rw [hτSdef]; field_simp
  obtain ⟨K, W₂, hK⟩ := SplusInf_decay d ψ c' hψ C κ τS (2 * (d : ℝ) - 4) hκ hτS hk
  set k : ℕ := 2 * d - 4 with hkdef
  have hkc : (k : ℝ) = 2 * (d : ℝ) - 4 := by
    rw [hkdef, Nat.cast_sub (by omega : 4 ≤ 2 * d)]; push_cast; ring
  refine ⟨|C k| + |K| * ((2 : ℝ) ^ (2 * (d : ℝ) - 4) + 1), max 1 W₂, by positivity, ?_⟩
  intro W hW s hs E hE z
  have hW1 : (1 : ℝ) ≤ W := le_trans (le_max_left _ _) hW
  have hW₂ : W₂ ≤ W := le_trans (le_max_right _ _) hW
  have hW0 : (0 : ℝ) < W := by linarith
  set r : ℝ := (zdInf z : ℝ) with hrdef
  set t : ℝ := r + W with htdef
  have hr : 0 ≤ r := Nat.cast_nonneg _
  have hWt : (W : ℝ) ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  set X : ℝ := (W : ℝ) ^ ((d : ℝ) - 4) * t ^ (-(2 * (d : ℝ) - 4)) with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hWτ : 1 ≤ (W : ℝ) ^ τc := Real.one_le_rpow hW1 hτc.le
  have hWd4 : 1 ≤ (W : ℝ) ^ ((d : ℝ) - 4) := Real.one_le_rpow hW1 (by linarith)
  have hwb : ValZ_wb d W (|C k| + |K| * ((2 : ℝ) ^ (2 * (d : ℝ) - 4) + 1)) τc z =
      (|C k| + |K| * ((2 : ℝ) ^ (2 * (d : ℝ) - 4) + 1)) * (W : ℝ) ^ τc * X := rfl
  rw [hwb]
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * (d : ℝ) - 4) := by positivity
  -- the kernel `s`
  have hs1 : ‖((s z : ℝ) : ℂ)‖ ≤ |C k| * X := by
    have h := hs.decay k z
    have hq : 1 + r / W = t / W := by rw [htdef]; field_simp; ring
    rw [hq] at h
    have hpos : 0 < (t / W) ^ k := by positivity
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 : |s z| ≤ C k / (W : ℝ) ^ d / (t / W) ^ k := by rw [le_div_iff₀ hpos]; exact h
    have hXe : C k / (W : ℝ) ^ d / (t / W) ^ k = C k * X := by
      have e1 : (W : ℝ) ^ ((d : ℝ) - 4) = (W : ℝ) ^ k / (W : ℝ) ^ d := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_sub hW0, hkc]; ring_nf
      have e2 : t ^ (-(2 * (d : ℝ) - 4)) = (t ^ k)⁻¹ := by
        rw [Real.rpow_neg ht0.le, ← hkc, Real.rpow_natCast]
      rw [hXdef, e1, e2, div_pow]
      field_simp
    rw [hXe] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hX0)
  -- the kernels `S^±_∞`
  have hind : (if r ≤ (W : ℝ) ^ (1 + τS) then ((W : ℝ) ^ d)⁻¹ else 0) ≤
      (2 : ℝ) ^ (2 * (d : ℝ) - 4) * ((W : ℝ) ^ τc * X) := by
    split_ifs with hr1
    · have hW1S : (W : ℝ) ≤ (W : ℝ) ^ (1 + τS) := by
        calc (W : ℝ) = (W : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
      have ht2 : t ≤ 2 * (W : ℝ) ^ (1 + τS) := by rw [htdef]; linarith
      have hneg : -(2 * (d : ℝ) - 4) ≤ 0 := by linarith
      have h3 : (2 * (W : ℝ) ^ (1 + τS)) ^ (-(2 * (d : ℝ) - 4)) ≤ t ^ (-(2 * (d : ℝ) - 4)) :=
        Real.rpow_le_rpow_of_nonpos ht0 ht2 hneg
      have e3 : (2 : ℝ) ^ (2 * (d : ℝ) - 4) * ((W : ℝ) ^ τc * ((W : ℝ) ^ ((d : ℝ) - 4) *
          (2 * (W : ℝ) ^ (1 + τS)) ^ (-(2 * (d : ℝ) - 4)))) = ((W : ℝ) ^ d)⁻¹ := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hW0.le,
          ← Real.rpow_natCast, ← Real.rpow_neg hW0.le]
        have e4 : (2 : ℝ) ^ (2 * (d : ℝ) - 4) * (2 : ℝ) ^ (-(2 * (d : ℝ) - 4)) = 1 := by
          rw [← Real.rpow_add (by norm_num)]; simp
        calc (2 : ℝ) ^ (2 * (d : ℝ) - 4) * ((W : ℝ) ^ τc * ((W : ℝ) ^ ((d : ℝ) - 4) *
              ((2 : ℝ) ^ (-(2 * (d : ℝ) - 4)) * (W : ℝ) ^ ((1 + τS) * -(2 * (d : ℝ) - 4)))))
            = ((2 : ℝ) ^ (2 * (d : ℝ) - 4) * (2 : ℝ) ^ (-(2 * (d : ℝ) - 4))) *
              ((W : ℝ) ^ τc * (W : ℝ) ^ ((d : ℝ) - 4) *
                (W : ℝ) ^ ((1 + τS) * -(2 * (d : ℝ) - 4))) := by ring
          _ = (W : ℝ) ^ (τc + ((d : ℝ) - 4) + (1 + τS) * -(2 * (d : ℝ) - 4)) := by
            rw [e4, one_mul, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
          _ = (W : ℝ) ^ (-(d : ℝ)) := by
            congr 1; nlinarith [hτSk]
      rw [← e3, hXdef]
      gcongr
    · positivity
  have htail : t ^ (-(2 * (d : ℝ) - 4)) ≤ (W : ℝ) ^ τc * X := by
    rw [hXdef, ← mul_assoc]
    exact le_mul_of_one_le_left (by positivity) (one_le_mul_of_one_le_of_one_le hWτ hWd4)
  have hSpm : ∀ v : ℂ, ‖v‖ ≤ K * ((if r ≤ (W : ℝ) ^ (1 + τS) then ((W : ℝ) ^ d)⁻¹ else 0) +
      t ^ (-(2 * (d : ℝ) - 4))) →
      ‖v‖ ≤ (|C k| + |K| * ((2 : ℝ) ^ (2 * (d : ℝ) - 4) + 1)) * (W : ℝ) ^ τc * X := by
    intro v hv
    have hnn : 0 ≤ (if r ≤ (W : ℝ) ^ (1 + τS) then ((W : ℝ) ^ d)⁻¹ else 0) +
        t ^ (-(2 * (d : ℝ) - 4)) := by
      have : 0 ≤ (if r ≤ (W : ℝ) ^ (1 + τS) then ((W : ℝ) ^ d)⁻¹ else 0) := by
        split_ifs <;> positivity
      positivity
    calc ‖v‖ ≤ |K| * ((if r ≤ (W : ℝ) ^ (1 + τS) then ((W : ℝ) ^ d)⁻¹ else 0) +
          t ^ (-(2 * (d : ℝ) - 4))) := hv.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hnn)
      _ ≤ |K| * ((2 : ℝ) ^ (2 * (d : ℝ) - 4) * ((W : ℝ) ^ τc * X) + (W : ℝ) ^ τc * X) := by
        gcongr
      _ = |K| * ((2 : ℝ) ^ (2 * (d : ℝ) - 4) + 1) * (W : ℝ) ^ τc * X := by ring
      _ ≤ _ := by
        gcongr
        linarith [abs_nonneg (C k)]
  have hK' := hK W hW₂ s hs E hE.le z
  refine ⟨hs1.trans ?_, hSpm _ hK'.1, hSpm _ hK'.2⟩
  calc |C k| * X ≤ |C k| * ((W : ℝ) ^ τc * X) := by
        gcongr; exact le_mul_of_one_le_left hX0 hWτ
    _ = |C k| * (W : ℝ) ^ τc * X := by ring
    _ ≤ _ := by
      gcongr
      have : 0 ≤ |K| * ((2 : ℝ) ^ (2 * (d : ℝ) - 4) + 1) := by positivity
      linarith

/-! ## One component and the product over the components -/

/-- A component in at most one of the two trees: from `v ≤ P u` with `u ≤ 1` and `u ≤ G`, the
value `v` is at most `P` times its black and blue factors. -/
private theorem ValZ_flag_one (v P u G : ℝ) (hP : 0 ≤ P) (hu1 : u ≤ 1) (huG : u ≤ G)
    (bk bu : Prop) [Decidable bk] [Decidable bu] (hv : v ≤ P * u) (hboth : bk → bu → False) :
    v ≤ P * (if bk then G else 1) * (if bu then G else 1) := by
  split_ifs with h1 h2
  · exact (hboth h1 h2).elim
  · simpa using hv.trans (mul_le_mul_of_nonneg_left huG hP)
  · simpa using hv.trans (mul_le_mul_of_nonneg_left huG hP)
  · simpa using hv.trans (mul_le_mul_of_nonneg_left hu1 hP)

/-- A waved edge, possibly in both trees: from `v ≤ P u²` with `0 ≤ u ≤ 1` and `u ≤ G`, the
value `v` is at most `P` times its black and blue factors. -/
private theorem ValZ_flag_two (v P u G : ℝ) (hP : 0 ≤ P) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (huG : u ≤ G) (bk bu : Prop) [Decidable bk] [Decidable bu] (hv : v ≤ P * (u * u)) :
    v ≤ P * (if bk then G else 1) * (if bu then G else 1) := by
  have hG : 0 ≤ G := hu0.trans huG
  have h1 : u * u ≤ G * G := mul_le_mul huG huG hu0 hG
  have h2 : u * u ≤ G := (mul_le_of_le_one_left hu0 hu1).trans huG
  have h3 : u * u ≤ 1 := (mul_le_of_le_one_left hu0 hu1).trans hu1
  split_ifs
  · nlinarith [mul_le_mul_of_nonneg_left h1 hP]
  · nlinarith [mul_le_mul_of_nonneg_left h2 hP]
  · nlinarith [mul_le_mul_of_nonneg_left h2 hP]
  · nlinarith [mul_le_mul_of_nonneg_left h3 hP]

/-- The bound of one component of a deterministic graph without dotted edge on `ℤ^d`, from
bounds `K_c W^{-d} u_w²` on the waved edges and `K_c W^{-q d/2} u_Θ` on the `Θ` edges of order
`q`, with `u_w, u_Θ ≤ min(1, G)`: the component is at most `K_c W^{-q d/2}` times `G` for each of
the two trees that contain it. -/
private theorem ValZ_comp_bound {V : Type*} {W : ℕ} (D : ValZ.Rec d) (N : ℕ) {Kc : ℝ}
    (hKc : 1 ≤ Kc) (G uw uθ : (Fin d → ℤ) → ℝ)
    (huw : ∀ z, 0 ≤ uw z ∧ uw z ≤ 1 ∧ uw z ≤ G z) (huθ : ∀ z, 0 ≤ uθ z ∧ uθ z ≤ 1 ∧ uθ z ≤ G z)
    (hwav : ∀ z, ‖D.S z‖ ≤ Kc * (W : ℝ) ^ (-(2 : ℝ) * d / 2) * (uw z * uw z) ∧
      ‖D.Sp z‖ ≤ Kc * (W : ℝ) ^ (-(2 : ℝ) * d / 2) * (uw z * uw z) ∧
      ‖D.Sm z‖ ≤ Kc * (W : ℝ) ^ (-(2 : ℝ) * d / 2) * (uw z * uw z))
    (σ : V → Fin d → ℤ) (c : Comp V) (hc : c.isDetKind N = true) (hdot : c.kind ≠ .dot)
    (hth : ∀ o, c.kind = .theta o → ∀ z,
      ‖D.chain o z‖ ≤ Kc * (W : ℝ) ^ (-(((Kind.theta o).ord : ℤ) : ℝ) * d / 2) * uθ z)
    (bk bu : Prop) [Decidable bk] [Decidable bu]
    (hbk : bk → c.kind.isDiffusive = true ∨ ∃ w, c.kind = .waved w)
    (hbu : bu → c.kind.isDiffusive = true ∨ c.kind.isBlue = true ∨ ∃ w, c.kind = .waved w)
    (hboth : bk → bu → ∃ w, c.kind = .waved w) :
    ‖ValZ.compVal D σ c‖ ≤ Kc * (W : ℝ) ^ (-((c.kind.ord : ℤ) : ℝ) * d / 2) *
      (if bk then G (σ c.y - σ c.x) else 1) * (if bu then G (σ c.y - σ c.x) else 1) := by
  have hK0 : 0 ≤ Kc := by linarith
  obtain ⟨κ, x, y, mi, lab⟩ := c
  set z := σ y - σ x with hz
  obtain ⟨hw0, hw1, hwG⟩ := huw z
  cases κ with
  | waved w =>
    have hord : (((Kind.waved w).ord : ℤ) : ℝ) = 2 := by simp [Kind.ord]
    simp only [hord]
    refine ValZ_flag_two _ _ _ _ (by positivity) hw0 hw1 hwG bk bu ?_
    obtain ⟨h1, h2, h3⟩ := hwav z
    cases w
    · exact h1
    · exact h2
    · exact h3
  | theta o =>
    obtain ⟨hθ0, hθ1, hθG⟩ := huθ z
    exact ValZ_flag_one _ _ _ _ (by positivity) hθ1 hθG bk bu (hth o rfl z)
      (fun h1 h2 => by obtain ⟨w, hw⟩ := hboth h1 h2; cases hw)
  | xdot =>
    have hbk' : ¬ bk := fun h => by
      rcases hbk h with h' | ⟨w, hw⟩
      · simp [Kind.isDiffusive] at h'
      · cases hw
    have hbu' : ¬ bu := fun h => by
      rcases hbu h with h' | h' | ⟨w, hw⟩
      · simp [Kind.isDiffusive] at h'
      · simp [Kind.isBlue] at h'
      · cases hw
    have hval : ‖ValZ.compVal D σ (⟨.xdot, x, y, mi, lab⟩ : Comp V)‖ ≤ 1 := by
      simp only [ValZ.compVal]
      split_ifs <;> simp
    simp only [hbk', hbu', ↓reduceIte, mul_one]
    have hord : ((Kind.xdot.ord : ℤ) : ℝ) = 0 := by simp [Kind.ord]
    rw [hord]
    simp only [neg_zero, zero_mul, zero_div, Real.rpow_zero, mul_one]
    linarith
  | dot => exact (hdot rfl).elim
  | G _ => simp [Comp.isDetKind] at hc
  | weight _ => simp [Comp.isDetKind] at hc
  | light _ => simp [Comp.isDetKind] at hc
  | inv _ => simp [Comp.isDetKind] at hc
  | wD _ _ => simp [Comp.isDetKind] at hc
  | thetaErr _ _ => simp [Comp.isDetKind] at hc
  | ghost => simp [Comp.isDetKind] at hc
  | aux _ _ _ => simp [Comp.isDetKind] at hc

/-- `(Π_{i ∈ l} c f(i)) = c^{|l|} Π_{i ∈ l} f(i)`. -/
private theorem ValZ_prod_map_const_mul {ι : Type*} (l : List ι) (c : ℝ) (f : ι → ℝ) :
    (l.map fun i => c * f i).prod = c ^ l.length * (l.map f).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons, ih, List.length_cons, pow_succ]; ring

/-- The product of the component bounds factors into the constant, the power of `W` and the
products of `c G` over the black and the blue list. -/
private theorem ValZ_prod_bound {k n : ℕ} (Γ : Graph k n) (Kc Wr c : ℝ) (hW : 0 < Wr)
    (B : Fin Γ.comps.length → ℝ) (bl bu : List (Fin Γ.comps.length)) (hbl : bl.Nodup)
    (hbu : bu.Nodup) :
    ∏ i : Fin Γ.comps.length, (Kc * Wr ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2) *
        (if i ∈ bl then c * B i else 1) * (if i ∈ bu then c * B i else 1)) =
      Kc ^ Γ.comps.length * Wr ^ (∑ i : Fin Γ.comps.length,
          (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2)) *
        (c ^ bl.length * c ^ bu.length) * ((bl.map B).prod * (bu.map B).prod) := by
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have h1 : ∏ i : Fin Γ.comps.length, (if i ∈ bl then c * B i else 1) =
      c ^ bl.length * (bl.map B).prod := by
    simp_rw [← List.mem_toFinset (l := bl)]
    rw [Finset.prod_ite_mem, Finset.univ_inter, List.prod_toFinset _ hbl, ValZ_prod_map_const_mul]
  have h2 : ∏ i : Fin Γ.comps.length, (if i ∈ bu then c * B i else 1) =
      c ^ bu.length * (bu.map B).prod := by
    simp_rw [← List.mem_toFinset (l := bu)]
    rw [Finset.prod_ite_mem, Finset.univ_inter, List.prod_toFinset _ hbu, ValZ_prod_map_const_mul]
  rw [h1, h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_sum_of_pos hW]
  ring

/-! ## [I, Cor 7.6] on `ℤ^d` -/

/-- `W^a t^{-a} ≤ 1` for `1 ≤ W ≤ t` and `a ≥ 0`. -/
private theorem ValZ_ratio_le {Wr t a : ℝ} (hW : 1 ≤ Wr) (ht : Wr ≤ t) (ha : 0 ≤ a) :
    Wr ^ a * t ^ (-a) ≤ 1 := by
  have ht0 : 0 < t := by linarith
  have h1 : Wr ^ a ≤ t ^ a := Real.rpow_le_rpow (by linarith) ht ha
  have h2 : t ^ a * t ^ (-a) = 1 := by rw [← Real.rpow_add ht0]; simp
  calc Wr ^ a * t ^ (-a) ≤ t ^ a * t ^ (-a) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 1 := h2

/-- The last step of [I, Cor 7.6] on `ℤ^d`: the constants and the losses `W^{τ/4}` are absorbed by
`⟨x − y⟩^{-τ/2} ≤ W^{-τ/2}`. -/
private theorem ValZ_final {Wr t CK Wx QR A B Wo e τ : ℝ} (hW : 1 ≤ Wr) (hWt : Wr ≤ t)
    (hτ : 0 < τ) (hCK : CK ≤ Wr ^ (τ / 4)) (hWx0 : 0 ≤ Wx)
    (hWx : Wx ≤ Wr ^ (τ / 4)) (hQR : QR * A = Wo) (hB : 0 ≤ B) (hWo : 0 ≤ Wo) :
    CK * Wx * QR * (A * B * t ^ (-(e - τ / 2))) ≤ Wo * B * t ^ (-(e - τ)) := by
  have hW0 : 0 < Wr := by linarith
  have ht0 : 0 < t := by linarith
  have hsplit : t ^ (-(e - τ / 2)) = t ^ (-(e - τ)) * t ^ (-(τ / 2)) := by
    rw [← Real.rpow_add ht0]; ring_nf
  have htτ : t ^ (-(τ / 2)) ≤ Wr ^ (-(τ / 2)) :=
    Real.rpow_le_rpow_of_nonpos hW0 hWt (by linarith)
  have hone : Wr ^ (τ / 4) * Wr ^ (τ / 4) * Wr ^ (-(τ / 2)) = 1 := by
    rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]
    ring_nf
    simp
  calc CK * Wx * QR * (A * B * t ^ (-(e - τ / 2)))
      = CK * Wx * (QR * A) * B * t ^ (-(e - τ)) * t ^ (-(τ / 2)) := by rw [hsplit]; ring
    _ = CK * Wx * Wo * B * t ^ (-(e - τ)) * t ^ (-(τ / 2)) := by rw [hQR]
    _ ≤ Wr ^ (τ / 4) * Wr ^ (τ / 4) * Wo * B * t ^ (-(e - τ)) * Wr ^ (-(τ / 2)) := by gcongr
    _ = (Wr ^ (τ / 4) * Wr ^ (τ / 4) * Wr ^ (-(τ / 2))) * (Wo * B * t ^ (-(e - τ))) := by ring
    _ = _ := by rw [hone, one_mul]

/-- [I, Cor 7.6] on `ℤ^d` for one family `k` of label kernels satisfying
[I, (2.13), (2.14), (2.16)]: the bound holds uniformly in `|E| < 2 − κ`. The black and blue lists
of components of the doubly connected internal form are spanning trees; each component is
bounded by a power of `W` times `W^d B^{d-2-τ₁}` for each tree containing it, and
[I, Claim 6.11] on `ℤ^d` sums the product. -/
private theorem ValZ_corBound_fixed (hd : 6 ≤ d) (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ)
    (cψ c' : ℝ) (hψ : ProfileShape ψ cψ) (hψ' : SymbolBound ψ c') (C : ℕ → ℝ) {κ : ℝ}
    (hκ : 0 < κ) (N : ℕ) (k : KerInf d) (hk : ∀ l, 4 ≤ l → l ≤ N → Even l → KerInfHyp k l)
    (n C' : ℕ) (Γ : Graph 2 n) (hNo : Γ.internalize.Normal C')
    (hDC : Γ.internalize.DoublyConnected) (hDet : Γ.comps.all (Comp.isDetKind N) = true)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
      ∀ E : ℝ, |E| < 2 - κ → ∀ x y : Fin d → ℤ,
        Summable (fun σ : Fin n → Fin d → ℤ =>
          ‖ValZ.term Γ (ValZ.rec s k W E) (Sum.elim ![x, y] σ)‖) ∧
        ValZ.absVal Γ (ValZ.rec s k W E) ![x, y] ≤
          (W : ℝ) ^ (-((Γ.ord : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
            ((zdInf (x - y) : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - τ)) := by
  obtain ⟨bl, bu, hbl, hbu', hbk, hbu, hboth, hTb, hTu⟩ := dc_trees (by norm_num) Γ C' hNo.1 hDC
  have hlb : bl.length = n + 1 := by have := tree_length bl _ hTb; omega
  have hlu : bu.length = n + 1 := by have := tree_length bu _ hTu; omega
  have hdot := no_dot Γ hNo.1
  have hd' : (6 : ℝ) ≤ d := by exact_mod_cast hd
  have hDi : ∀ i : Fin Γ.comps.length, Γ.comps[i].isDetKind N = true := fun i =>
    List.all_eq_true.1 hDet _ (List.getElem_mem _)
  set Γa : AuxGraph n := ⟨bl.map fun i => (Γ.comps[i].x, Γ.comps[i].y),
    bu.map fun i => (Γ.comps[i].x, Γ.comps[i].y, 0)⟩ with hΓa
  have hTa : TreeEdges Γa.black := hTb
  have hUa : TreeEdges (Γa.blue.map fun e => (e.1, e.2.1)) := by
    simpa [hΓa, List.map_map, Function.comp_def] using hTu
  obtain ⟨τ₁, hτ₁, W₁, hW₁⟩ := auxTreeZStrong d hd Γa hTa hUa (τ / 2) (by positivity)
  set τc : ℝ := min (min τ₁ 1) (τ / (4 * ((Γ.comps.length : ℝ) + 1))) with hτcdef
  have hL0 : (0 : ℝ) ≤ Γ.comps.length := Nat.cast_nonneg _
  have hτc0 : 0 < τc := lt_min (lt_min hτ₁ one_pos) (by positivity)
  have hτcτ₁ : τc ≤ τ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hτc1 : τc ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hτcL : τc * Γ.comps.length ≤ τ / 4 := by
    have h1 : τc ≤ τ / (4 * ((Γ.comps.length : ℝ) + 1)) := min_le_right _ _
    have h2 : τc * Γ.comps.length ≤ τ / (4 * ((Γ.comps.length : ℝ) + 1)) * Γ.comps.length :=
      mul_le_mul_of_nonneg_right h1 hL0
    refine h2.trans ?_
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨Kw, Ww, hKw0, hw⟩ := ValZ_wave_bound hd ψ c' hψ' C hκ hτc0
  have hth : ∀ i : Fin Γ.comps.length, ∃ W₀ : ℝ, ∀ o, Γ.comps[i].kind = .theta o → ∀ W : ℕ, W₀ ≤ W →
      ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s → ∀ z : Fin d → ℤ,
        ‖chainZ s k W o z‖ ≤ (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
          ((W : ℝ) ^ (-2 : ℝ) * ((zdInf z : ℝ) + W) ^ (-((d : ℝ) - 2 - τc))) := by
    intro i
    by_cases h : ∃ o, Γ.comps[i].kind = .theta o
    · obtain ⟨o, ho⟩ := h
      have hl : labelOK N o = true := by
        have := hDi i
        simp only [Comp.isDetKind, ho, Bool.and_eq_true] at this
        exact this.2
      have hK : ∀ l ∈ o, KerInfHyp k l := by
        intro l hlo
        simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
          at hl
        obtain ⟨⟨h4, hN⟩, h2⟩ := hl l hlo
        exact hk l h4 hN (Nat.even_iff.2 h2)
      obtain ⟨W₀, hW₀⟩ := chainInf d hd ψ cψ hψ C k o hK τc hτc0
      refine ⟨W₀, fun o' ho' => ?_⟩
      rw [ho] at ho'
      cases ho'
      exact hW₀
    · exact ⟨0, fun o ho => (h ⟨o, ho⟩).elim⟩
  choose Wth hWth using hth
  obtain ⟨Cc, hCc0, hCc⟩ := ValZ_coeff_bound hκ Γ.coeff
  set Kw' : ℝ := max 1 Kw with hKw'
  have hKw'1 : 1 ≤ Kw' := le_max_left _ _
  refine ⟨max (max 1 (max Ww (∑ i, |Wth i|)))
    (max W₁ ((max 1 (Cc * Kw' ^ Γ.comps.length)) ^ (4 / τ))),
    fun W hW s hs E hE x y => ?_⟩
  have hWa : max 1 (max Ww (∑ i, |Wth i|)) ≤ (W : ℝ) := (le_max_left _ _).trans hW
  have hWb : max W₁ ((max 1 (Cc * Kw' ^ Γ.comps.length)) ^ (4 / τ)) ≤ (W : ℝ) :=
    (le_max_right _ _).trans hW
  have hW1 : (1 : ℝ) ≤ W := (le_max_left _ _).trans hWa
  have hW1n : 1 ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  set D := ValZ.rec s k W E with hD
  set β : ℝ := (d : ℝ) - 2 - τ₁ with hβ
  set Kc : ℝ := Kw' * (W : ℝ) ^ τc with hKc
  have hWτc : 1 ≤ (W : ℝ) ^ τc := Real.one_le_rpow hW1 hτc0.le
  have hKc1 : 1 ≤ Kc := one_le_mul_of_one_le_of_one_le hKw'1 hWτc
  set G : (Fin d → ℤ) → ℝ := fun z =>
    (W : ℝ) ^ (d : ℝ) * ((W : ℝ) ^ (-2 : ℝ) * ((zdInf z : ℝ) + W) ^ (-β)) with hG
  set uw : (Fin d → ℤ) → ℝ := fun z =>
    (W : ℝ) ^ ((d : ℝ) - 2) * ((zdInf z : ℝ) + W) ^ (-((d : ℝ) - 2)) with huwdef
  set uθ : (Fin d → ℤ) → ℝ := fun z =>
    (W : ℝ) ^ ((d : ℝ) - 2 - τc) * ((zdInf z : ℝ) + W) ^ (-((d : ℝ) - 2 - τc)) with huθdef
  have hWt : ∀ z : Fin d → ℤ, (W : ℝ) ≤ (zdInf z : ℝ) + W := fun z => by
    linarith [(Nat.cast_nonneg (zdInf z) : (0 : ℝ) ≤ zdInf z)]
  have hGe : ∀ z : Fin d → ℤ, G z =
      (W : ℝ) ^ ((d : ℝ) - 2) * ((zdInf z : ℝ) + W) ^ (-β) := fun z => by
    rw [hG]
    simp only
    rw [← mul_assoc, ← Real.rpow_add hW0]
    ring_nf
  have huw : ∀ z, 0 ≤ uw z ∧ uw z ≤ 1 ∧ uw z ≤ G z := by
    intro z
    have ht1 : (1 : ℝ) ≤ (zdInf z : ℝ) + W := hW1.trans (hWt z)
    refine ⟨by positivity, ValZ_ratio_le hW1 (hWt z) (by linarith), ?_⟩
    rw [hGe]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith))
      (by positivity)
  have huθ : ∀ z, 0 ≤ uθ z ∧ uθ z ≤ 1 ∧ uθ z ≤ G z := by
    intro z
    have ht1 : (1 : ℝ) ≤ (zdInf z : ℝ) + W := hW1.trans (hWt z)
    refine ⟨by positivity, ValZ_ratio_le hW1 (hWt z) (by linarith), ?_⟩
    rw [hGe]
    exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith))
      (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) (by positivity) (by positivity)
  have hwav : ∀ z, ‖D.S z‖ ≤ Kc * (W : ℝ) ^ (-(2 : ℝ) * d / 2) * (uw z * uw z) ∧
      ‖D.Sp z‖ ≤ Kc * (W : ℝ) ^ (-(2 : ℝ) * d / 2) * (uw z * uw z) ∧
      ‖D.Sm z‖ ≤ Kc * (W : ℝ) ^ (-(2 : ℝ) * d / 2) * (uw z * uw z) := by
    intro z
    have hWw : Ww ≤ (W : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hWa)
    obtain ⟨h1, h2, h3⟩ := hw W hWw s hs E hE z
    have ht0 : 0 < (zdInf z : ℝ) + W := by linarith [hWt z]
    have e : ValZ_wb d W Kw τc z ≤ Kc * (W : ℝ) ^ (-(2 : ℝ) * d / 2) * (uw z * uw z) := by
      have e1 : (W : ℝ) ^ ((d : ℝ) - 4) * ((zdInf z : ℝ) + W) ^ (-(2 * (d : ℝ) - 4)) =
          (W : ℝ) ^ (-(2 : ℝ) * d / 2) * (uw z * uw z) := by
        simp only [huwdef]
        have ea : (W : ℝ) ^ (-(2 : ℝ) * d / 2) * ((W : ℝ) ^ ((d : ℝ) - 2) *
            ((zdInf z : ℝ) + W) ^ (-((d : ℝ) - 2)) * ((W : ℝ) ^ ((d : ℝ) - 2) *
            ((zdInf z : ℝ) + W) ^ (-((d : ℝ) - 2)))) =
            ((W : ℝ) ^ (-(2 : ℝ) * d / 2) * (W : ℝ) ^ ((d : ℝ) - 2) * (W : ℝ) ^ ((d : ℝ) - 2)) *
              (((zdInf z : ℝ) + W) ^ (-((d : ℝ) - 2)) *
                ((zdInf z : ℝ) + W) ^ (-((d : ℝ) - 2))) := by
          ring
        rw [ea, ← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add ht0]
        congr 2 <;> ring
      unfold ValZ_wb
      rw [e1, hKc, mul_assoc (Kw' * (W : ℝ) ^ τc)]
      gcongr
      exact le_max_right 1 Kw
    exact ⟨h1.trans e, h2.trans e, h3.trans e⟩
  have hcomp : ∀ (σ' : Atom 2 n → Fin d → ℤ) (i : Fin Γ.comps.length),
      ‖ValZ.compVal D σ' Γ.comps[i]‖ ≤ Kc * (W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2) *
        (if i ∈ bl then G (σ' Γ.comps[i].y - σ' Γ.comps[i].x) else 1) *
        (if i ∈ bu then G (σ' Γ.comps[i].y - σ' Γ.comps[i].x) else 1) := by
    intro σ' i
    refine ValZ_comp_bound D N hKc1 G uw uθ huw huθ hwav σ' Γ.comps[i] (hDi i)
      (hdot _ (List.getElem_mem _)) (fun o ho z => ?_) _ _ (hbk i) (hbu i) (hboth i)
    have hWi : Wth i ≤ (W : ℝ) := by
      refine le_trans ?_ ((le_max_right _ _).trans ((le_max_right _ _).trans hWa))
      exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Wth j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ _))
    have h1 := hWth i o ho W hWi s hs z
    have ht0 : 0 < (zdInf z : ℝ) + W := by linarith [hWt z]
    refine h1.trans ?_
    have e1 : (W : ℝ) ^ (-((((Kind.theta o).ord : ℤ) : ℝ) - 2) * d / 2) *
        ((W : ℝ) ^ (-2 : ℝ) * ((zdInf z : ℝ) + W) ^ (-((d : ℝ) - 2 - τc))) =
        (W : ℝ) ^ τc * (W : ℝ) ^ (-(((Kind.theta o).ord : ℤ) : ℝ) * d / 2) * uθ z := by
      simp only [huθdef]
      have ea : (W : ℝ) ^ τc * (W : ℝ) ^ (-(((Kind.theta o).ord : ℤ) : ℝ) * d / 2) *
          ((W : ℝ) ^ ((d : ℝ) - 2 - τc) * ((zdInf z : ℝ) + W) ^ (-((d : ℝ) - 2 - τc))) =
          ((W : ℝ) ^ τc * (W : ℝ) ^ (-(((Kind.theta o).ord : ℤ) : ℝ) * d / 2) *
            (W : ℝ) ^ ((d : ℝ) - 2 - τc)) * ((zdInf z : ℝ) + W) ^ (-((d : ℝ) - 2 - τc)) := by ring
      rw [ea, ← mul_assoc, ← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
      congr 2
      ring
    rw [e1, hKc]
    gcongr
    exact le_mul_of_one_le_left (by positivity) hKw'1
  -- the auxiliary graph of the two trees, with blue kernels `B^β`
  set A : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ := fun _ p r => AuxTreeZ.bB d W β p r with hA
  have hAb : ∀ j p r, |A j p r| ≤ AuxTreeZ.bB d W ((d : ℝ) - 2 - τ₁) p r := fun j p r => by
    rw [abs_of_pos (AuxTreeZ.bB_pos hW1n _ _ _)]
  have hW₁' : W₁ ≤ (W : ℝ) := (le_max_left _ _).trans hWb
  obtain ⟨hsumZ, hvalZ⟩ := hW₁ W hW₁' A hAb x y
  set M : ℝ := Cc * (Kc ^ Γ.comps.length * (W : ℝ) ^ (∑ i : Fin Γ.comps.length,
      (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2)) *
      (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ (d : ℝ)) ^ bu.length)) with hM
  have hM0 : 0 ≤ M := by positivity
  have hpt : ∀ σ : Fin n → Fin d → ℤ, ‖ValZ.term Γ D (Sum.elim ![x, y] σ)‖ ≤
      M * Γa.termZ d W β A x y σ := by
    intro σ
    set σ' : Atom 2 n → Fin d → ℤ := Sum.elim ![x, y] σ with hσ'
    set B : Fin Γ.comps.length → ℝ := fun i =>
      AuxTreeZ.bB d W β (σ' Γ.comps[i].x) (σ' Γ.comps[i].y) with hBdef
    have hB : ∀ i : Fin Γ.comps.length,
        G (σ' Γ.comps[i].y - σ' Γ.comps[i].x) = (W : ℝ) ^ (d : ℝ) * B i := by
      intro i
      simp only [hG, hBdef, AuxTreeZ.bB, AuxTreeZ.brk]
      rw [← neg_sub, zdInf_neg]
    have h1 : ∏ i : Fin Γ.comps.length, ‖ValZ.compVal D σ' Γ.comps[i]‖ ≤
        ∏ i : Fin Γ.comps.length, (Kc * (W : ℝ) ^ (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2) *
          (if i ∈ bl then (W : ℝ) ^ (d : ℝ) * B i else 1) *
          (if i ∈ bu then (W : ℝ) ^ (d : ℝ) * B i else 1)) := by
      refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
      rw [← hB i]
      exact hcomp σ' i
    rw [ValZ_prod_bound Γ Kc W ((W : ℝ) ^ (d : ℝ)) hW0 B bl bu hbl hbu'] at h1
    have htermZ : Γa.termZ d W β A x y σ = (bl.map B).prod * (bu.map B).prod := by
      simp only [AuxGraph.termZ, hΓa, List.map_map, Function.comp_def, hA]
      congr 2
      refine List.map_congr_left fun i _ => ?_
      exact abs_of_pos (AuxTreeZ.bB_pos hW1n _ _ _)
    rw [htermZ]
    unfold ValZ.term
    rw [norm_mul, List.norm_prod, List.map_map, ← Fin.prod_univ_fun_getElem]
    calc ‖Γ.coeff.eval D.m‖ * ∏ i : Fin Γ.comps.length, (norm ∘ ValZ.compVal D σ') Γ.comps[i]
        ≤ Cc * (Kc ^ Γ.comps.length * (W : ℝ) ^ (∑ i : Fin Γ.comps.length,
            (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2)) *
            (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ (d : ℝ)) ^ bu.length) *
            ((bl.map B).prod * (bu.map B).prod)) :=
          mul_le_mul (hCc E hE) h1 (Finset.prod_nonneg fun i _ => norm_nonneg _) hCc0
      _ = M * ((bl.map B).prod * (bu.map B).prod) := by rw [hM]; ring
  have hsum : Summable (fun σ : Fin n → Fin d → ℤ => ‖ValZ.term Γ D (Sum.elim ![x, y] σ)‖) :=
    Summable.of_nonneg_of_le (fun σ => norm_nonneg _) hpt (hsumZ.mul_left M)
  refine ⟨hsum, ?_⟩
  have habs : ValZ.absVal Γ D ![x, y] ≤ M * Γa.valZ d W β A x y := by
    unfold ValZ.absVal AuxGraph.valZ
    rw [← tsum_mul_left]
    exact hsum.tsum_le_tsum hpt (hsumZ.mul_left M)
  refine habs.trans ((mul_le_mul_of_nonneg_left hvalZ hM0).trans ?_)
  -- the powers of `W`
  set t : ℝ := AuxTreeZ.brk d W x y with htdef
  have htW : (W : ℝ) ≤ t := AuxTreeZ.W_le_brk x y
  have hCK : Cc * Kw' ^ Γ.comps.length ≤ (W : ℝ) ^ (τ / 4) :=
    const_le_rpow _ τ W hτ ((le_max_right _ _).trans hWb)
  have hKcL : Kc ^ Γ.comps.length =
      Kw' ^ Γ.comps.length * (W : ℝ) ^ (τc * Γ.comps.length) := by
    rw [hKc, mul_pow, ← Real.rpow_natCast ((W : ℝ) ^ τc), ← Real.rpow_mul hW0.le]
  have hτcW : (W : ℝ) ^ (τc * Γ.comps.length) ≤ (W : ℝ) ^ (τ / 4) :=
    Real.rpow_le_rpow_of_exponent_le hW1 hτcL
  have hexp : (W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2)) *
      (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ (d : ℝ)) ^ bu.length) *
      (W : ℝ) ^ (-((2 * (n : ℝ) + 4) * d / 2)) = (W : ℝ) ^ (-((Γ.ord : ℝ) * d / 2)) := by
    rw [hlb, hlu, ← Real.rpow_natCast ((W : ℝ) ^ (d : ℝ)), ← Real.rpow_mul hW0.le,
      ← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_add hW0]
    congr 1
    rw [ord_eq_sum, ← Finset.sum_div, ← Finset.sum_mul, Finset.sum_neg_distrib]
    push_cast
    ring
  have hdef : ((zdInf (x - y) : ℝ) + W) = t := rfl
  rw [hdef]
  have hM' : M = (Cc * Kw' ^ Γ.comps.length) * (W : ℝ) ^ (τc * Γ.comps.length) *
      ((W : ℝ) ^ (∑ i : Fin Γ.comps.length, (-((Γ.comps[i].kind.ord : ℤ) : ℝ) * d / 2)) *
        (((W : ℝ) ^ (d : ℝ)) ^ bl.length * ((W : ℝ) ^ (d : ℝ)) ^ bu.length)) := by
    rw [hM, hKcL]; ring
  rw [hM']
  exact ValZ_final hW1 htW hτ hCK (by positivity) hτcW hexp (by positivity) (by positivity)

/-- The label kernels `K(E)` satisfy [I, (2.13), (2.14), (2.16)] (`KerInfHyp`) at the even orders
`l ∈ [4, N]` along every choice of energies `E(W)` with `|E(W)| < 2 − κ`: the family
`l, W ↦ K(E(W)) l W` satisfies `KerInfHyp` at `l`. -/
def ValZ.SelUnif (κ : ℝ) (N : ℕ) (K : ℝ → KerInf d) : Prop :=
  ∀ Esel : ℕ → ℝ, (∀ W, |Esel W| < 2 - κ) →
    ∀ l, 4 ≤ l → l ≤ N → Even l → KerInfHyp (fun l W => K (Esel W) l W) l

/-- **[I, Cor 7.6] = [I, (8.7)] on `ℤ^d`**: for `d ≥ 6`, a profile shape `ψ` with
`−1 + c' ≤ ψ ≤ 1`, the constants `C`, `κ > 0`, label kernels `K(E)` with `ValZ.SelUnif κ N K` and
a deterministic graph `Γ` (waved, `×`-dotted and `Θ` edges with labels in `[4, N]`) whose internal
form is normal regular and doubly connected: for every `τ > 0` there is `W₀` such that for
`W ≥ W₀`, every kernel `s` of `InfKernel ψ C W`, `|E| < 2 − κ` and `x, y ∈ ℤ^d`, the summand of
the absolute value is summable and
`|Γ^∞|^{abs}_{xy} ≤ W^{-n_Γ d/2} W^{2d-4} (|x − y| + W)^{-(2d-4-τ)}`. -/
theorem ValZ.corBound :
  ∀ (d : ℕ), 6 ≤ d → ∀ (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) (cψ c' : ℝ),
    ProfileShape ψ cψ → SymbolBound ψ c' → ∀ (C : ℕ → ℝ) (κ : ℝ), 0 < κ →
    ∀ (N : ℕ) (K : ℝ → KerInf d), ValZ.SelUnif κ N K →
    ∀ (n C' : ℕ) (Γ : Graph 2 n), Γ.internalize.Normal C' → Γ.internalize.DoublyConnected →
      Γ.comps.all (Comp.isDetKind N) = true →
      ∀ τ : ℝ, 0 < τ → ∃ W₀ : ℝ, ∀ W : ℕ, W₀ ≤ W → ∀ s : (Fin d → ℤ) → ℝ, InfKernel ψ C W s →
        ∀ E : ℝ, |E| < 2 - κ → ∀ x y : Fin d → ℤ,
          Summable (fun σ : Fin n → Fin d → ℤ =>
            ‖ValZ.term Γ (ValZ.rec s (K E) W E) (Sum.elim ![x, y] σ)‖) ∧
          ValZ.absVal Γ (ValZ.rec s (K E) W E) ![x, y] ≤
            (W : ℝ) ^ (-((Γ.ord : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
              ((zdInf (x - y) : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - τ)) := by
  intro d hd ψ cψ c' hψ hψ' C κ hκ N K hK n C' Γ hNo hDC hDet τ hτ
  obtain ⟨W₀, hW₀⟩ := ValZ_uniform (κ := κ) (fun E W => ∀ s : (Fin d → ℤ) → ℝ,
      InfKernel ψ C W s → ∀ x y : Fin d → ℤ,
        Summable (fun σ : Fin n → Fin d → ℤ =>
          ‖ValZ.term Γ (ValZ.rec s (K E) W E) (Sum.elim ![x, y] σ)‖) ∧
        ValZ.absVal Γ (ValZ.rec s (K E) W E) ![x, y] ≤
          (W : ℝ) ^ (-((Γ.ord : ℝ) * d / 2)) * (W : ℝ) ^ (2 * (d : ℝ) - 4) *
            ((zdInf (x - y) : ℝ) + W) ^ (-(2 * (d : ℝ) - 4 - τ)))
    (fun Esel hsel => by
      obtain ⟨W₀, h⟩ := ValZ_corBound_fixed hd ψ cψ c' hψ hψ' C hκ N
        (fun l W => K (Esel W) l W) (hK Esel hsel) n C' Γ hNo hDC hDet τ hτ
      exact ⟨W₀, fun W hW s hs x y => h W hW s hs (Esel W) (hsel W) x y⟩)
  exact ⟨W₀, fun W hW s hs E hE x y => hW₀ W hW E hE s hs x y⟩

/-! ## [I, Def 8.2] on `ℤ^d` -/

/-- The subtraction of [I, (8.3)] on `ℤ^d`: `f − [Σ_y f(y)] s` where `Σ_y s(y) = 1`, and
`f − [Σ_y f(y)] δ_0` elsewhere, so that the row sum is `0` at every `W`. -/
def ValZ.renorm (s : (Fin d → ℤ) → ℝ) (f : (Fin d → ℤ) → ℂ) (x : Fin d → ℤ) : ℂ :=
  f x - (∑' y, f y) * (if ∑' y, s y = 1 then (s x : ℂ) else if x = 0 then 1 else 0)

/-- Where `Σ_y s(y) = 1`, `ValZ.renorm` is the subtraction `f − [Σ_y f(y)] s` of [I, (8.3)]. -/
theorem ValZ.renorm_of_tsum {s : (Fin d → ℤ) → ℝ} (h : ∑' y, s y = 1) (f : (Fin d → ℤ) → ℂ)
    (x : Fin d → ℤ) : ValZ.renorm s f x = f x - (∑' y, f y) * (s x : ℂ) := by
  simp [ValZ.renorm, h]

/-- The row sum of `ValZ.renorm s f` is `0`, for every `s` and `f`. -/
theorem ValZ.tsum_renorm (s : (Fin d → ℤ) → ℝ) (f : (Fin d → ℤ) → ℂ) :
    ∑' x, ValZ.renorm s f x = 0 := by
  classical
  set g : (Fin d → ℤ) → ℂ := fun x =>
    if ∑' y, s y = 1 then (s x : ℂ) else if x = 0 then 1 else 0 with hgdef
  have hg : HasSum g 1 := by
    by_cases h : ∑' y, s y = 1
    · have hsum : Summable s := by
        by_contra hns
        rw [tsum_eq_zero_of_not_summable hns] at h
        norm_num at h
      have h1 : HasSum (fun x => (s x : ℂ)) ((∑' y, s y : ℝ) : ℂ) :=
        Complex.hasSum_ofReal.2 hsum.hasSum
      rw [h, Complex.ofReal_one] at h1
      simpa [hgdef, h] using h1
    · simpa [hgdef, h] using hasSum_ite_eq (0 : Fin d → ℤ) (1 : ℂ)
  have hr : ∀ x, ValZ.renorm s f x = f x - (∑' y, f y) * g x := fun x => rfl
  simp only [hr]
  by_cases hf : Summable f
  · rw [(hf.hasSum.sub (hg.mul_left (∑' y, f y))).tsum_eq]
    ring
  · rw [tsum_eq_zero_of_not_summable hf]
    simp only [zero_mul, sub_zero]
    exact tsum_eq_zero_of_not_summable hf

/-- `ValZ.renorm s f` is even when `s` and `f` are. -/
theorem ValZ.renorm_neg {s : (Fin d → ℤ) → ℝ} (hs : ∀ x, s (-x) = s x) {f : (Fin d → ℤ) → ℂ}
    (hf : ∀ x, f (-x) = f x) (x : Fin d → ℤ) : ValZ.renorm s f (-x) = ValZ.renorm s f x := by
  simp only [ValZ.renorm, hs, hf, neg_eq_zero]

/-- The kernels `Σ̊^∞_l` of the orders `l < N` ([I, Def 8.2] on `ℤ^d`) at the kernel `s`, the band
width `W` and the energy `E`, as functions of the offset: the entry `l < N` is the subtraction
`ValZ.renorm` of the value of `Sig l` at `(0, x)` on the record whose labels read the entries below
`l`; the entries `≥ N` are `0`. -/
def ValZ.sigUpTo (Sig : ℕ → Expansion 2) (s : (Fin d → ℤ) → ℝ) (W : ℕ) (E : ℝ) :
    ℕ → ℕ → (Fin d → ℤ) → ℂ
  | 0 => fun _ _ => 0
  | N + 1 => Function.update (ValZ.sigUpTo Sig s W E N) N
      (ValZ.renorm s fun x =>
        ValZ.expVal (Sig N) (ValZ.rec s (fun l _ => ValZ.sigUpTo Sig s W E N l) W E) ![0, x])

/-- `Σ^{(r),∞}_l(0, x)` of [I, Def 8.2] on `ℤ^d`: the value of `Sig l` at `(0, x)` on the record
whose labelled `Θ` edges read `Σ̊^∞` of the orders below `l`. -/
def ValZ.sigR (Sig : ℕ → Expansion 2) (s : (Fin d → ℤ) → ℝ) (W : ℕ) (E : ℝ) (l : ℕ)
    (x : Fin d → ℤ) : ℂ :=
  ValZ.expVal (Sig l) (ValZ.rec s (fun l' _ => ValZ.sigUpTo Sig s W E l l') W E) ![0, x]

/-- `Σ̊^∞_l(0, x) = Σ^{(r),∞}_l(0, x) − [Σ_y Σ^{(r),∞}_l(0, y)] S_∞(x)` of [I, (8.3)] on `ℤ^d`
(`δ_0` in place of `S_∞` where `Σ_y s(y) ≠ 1`). -/
def ValZ.sigRing (Sig : ℕ → Expansion 2) (s : (Fin d → ℤ) → ℝ) (W : ℕ) (E : ℝ) (l : ℕ) :
    (Fin d → ℤ) → ℂ :=
  ValZ.renorm s (ValZ.sigR Sig s W E l)

/-- The entries of `ValZ.sigUpTo` below `N` are the kernels `Σ̊^∞_l`. -/
theorem ValZ.sigUpTo_eq (Sig : ℕ → Expansion 2) (s : (Fin d → ℤ) → ℝ) (W : ℕ) (E : ℝ) :
    ∀ {N l : ℕ}, l < N → ValZ.sigUpTo Sig s W E N l = ValZ.sigRing Sig s W E l := by
  intro N
  induction N with
  | zero => intro l hl; omega
  | succ N ih =>
    intro l hl
    by_cases h : l = N
    · subst h
      simp only [ValZ.sigUpTo, Function.update_self]
      rfl
    · rw [ValZ.sigUpTo, Function.update_of_ne h]
      exact ih (by omega)

/-- The family `E ↦ Σ̊^∞(E)` of label kernels at `S_∞ = Sinf ψ W` ([I, (7.3)]):
`(l, W, x) ↦ Σ̊^∞_l(0, x)`. -/
def ValZ.sigKer (Sig : ℕ → Expansion 2) (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) (E : ℝ) :
    KerInf d :=
  fun l W x => ValZ.sigRing Sig (Sinf ψ W) W E l x

/-- The number `R(E, W) = Σ_{x ∈ ℤ^d} Σ^{(r),∞}_n(0, x)` of [I, (8.8)], at `S_∞ = Sinf ψ W`. -/
def ValZ.rowSum (Sig : ℕ → Expansion 2) (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) (n : ℕ)
    (E : ℝ) (W : ℕ) : ℂ :=
  ∑' x, ValZ.sigR Sig (Sinf ψ W) W E n x

/-- The value of a formal sum at `(0, x)` on an even record is even in `x`. -/
private theorem ValZ_expVal_neg {D : ValZ.Rec d} (hD : D.Even) (F : Expansion 2)
    (x : Fin d → ℤ) : ValZ.expVal F D ![0, -x] = ValZ.expVal F D ![0, x] := by
  unfold ValZ.expVal
  congr 1
  refine List.map_congr_left fun g _ => ?_
  rw [← ValZ.val_neg g.2 hD ![0, x]]
  congr 1
  funext i
  fin_cases i <;> simp

/-- The entries of `ValZ.sigUpTo` are even when `s` is. -/
private theorem ValZ_sigUpTo_neg (Sig : ℕ → Expansion 2) {s : (Fin d → ℤ) → ℝ}
    (hs : ∀ x, s (-x) = s x) (W : ℕ) (E : ℝ) :
    ∀ N l x, ValZ.sigUpTo Sig s W E N l (-x) = ValZ.sigUpTo Sig s W E N l x := by
  intro N
  induction N with
  | zero => intro l x; rfl
  | succ N ih =>
    intro l x
    by_cases h : l = N
    · subst h
      simp only [ValZ.sigUpTo, Function.update_self]
      exact ValZ.renorm_neg hs (fun y => ValZ_expVal_neg
        (ValZ.rec_even hs W (fun l' y => ih l' y) E) _ y) x
    · simp only [ValZ.sigUpTo, Function.update_of_ne h]
      exact ih l x

/-- `Σ^{(r),∞}_l(0, ·)` is even when `s` is, at every `W` and `E`. -/
theorem ValZ.sigR_neg (Sig : ℕ → Expansion 2) {s : (Fin d → ℤ) → ℝ} (hs : ∀ x, s (-x) = s x)
    (W : ℕ) (E : ℝ) (l : ℕ) (x : Fin d → ℤ) :
    ValZ.sigR Sig s W E l (-x) = ValZ.sigR Sig s W E l x :=
  ValZ_expVal_neg (ValZ.rec_even hs W (fun l' y => ValZ_sigUpTo_neg Sig hs W E l l' y) E) _ x

/-- **Evenness of `Σ̊^∞_l`** ([I, (8.6)] on `ℤ^d`): `Σ̊^∞_l(0, −x) = Σ̊^∞_l(0, x)` at every `W` and
`E`. -/
theorem ValZ.sigKer_neg (Sig : ℕ → Expansion 2) (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ)
    (E : ℝ) (l W : ℕ) (x : Fin d → ℤ) : ValZ.sigKer Sig ψ E l W (-x) = ValZ.sigKer Sig ψ E l W x :=
  ValZ.renorm_neg (ValZ.Sinf_neg ψ W) (ValZ.sigR_neg Sig (ValZ.Sinf_neg ψ W) W E l) x

/-- **Row sum zero of `Σ̊^∞_l`** ([I, (8.3)] on `ℤ^d`): `Σ_x Σ̊^∞_l(0, x) = 0` at every `W` and
`E`. -/
theorem ValZ.tsum_sigKer (Sig : ℕ → Expansion 2) (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ)
    (E : ℝ) (l W : ℕ) : ∑' x, ValZ.sigKer Sig ψ E l W x = 0 :=
  ValZ.tsum_renorm _ _

/-- Where `Σ_x S_∞(x) = 1`, in particular for `W ≥ W₀` (`InfKernel.sum_one`), `Σ̊^∞_l` is
`Σ^{(r),∞}_l − [Σ_y Σ^{(r),∞}_l(0, y)] S_∞` of [I, (8.3)]. -/
theorem ValZ.sigKer_of_tsum (Sig : ℕ → Expansion 2)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) (E : ℝ) (l W : ℕ)
    (h : ∑' y, Sinf ψ W y = 1) (x : Fin d → ℤ) :
    ValZ.sigKer Sig ψ E l W x = ValZ.sigR Sig (Sinf ψ W) W E l x -
      (∑' y, ValZ.sigR Sig (Sinf ψ W) W E l y) * (Sinf ψ W x : ℂ) :=
  ValZ.renorm_of_tsum h _ x

/-- The labelled `Θ` edges of `Σ^{(r),∞}_l` read `Σ̊^∞ = ValZ.sigKer` at the orders below `l`:
the chains of the record of `ValZ.sigR` and of `ValZ.rec (Sinf ψ W) (ValZ.sigKer Sig ψ E) W E`
agree on every label with entries below `l`. -/
theorem ValZ.chain_sigR (Sig : ℕ → Expansion 2) (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ)
    (W : ℕ) (E : ℝ) (l : ℕ) (o : List ℕ) (ho : ∀ j ∈ o, j < l) :
    chainZ (Sinf ψ W) (fun l' _ => ValZ.sigUpTo Sig (Sinf ψ W) W E l l') W o =
      chainZ (Sinf ψ W) (ValZ.sigKer Sig ψ E) W o := by
  unfold chainZ
  suffices h : ∀ F : (Fin d → ℤ) → ℂ, ∀ o : List ℕ, (∀ j ∈ o, j < l) →
      o.foldl (fun F l' => convZ (convZ F (ValZ.sigUpTo Sig (Sinf ψ W) W E l l'))
        (ThetaInf (Sinf ψ W))) F =
      o.foldl (fun F l' => convZ (convZ F (ValZ.sigKer Sig ψ E l' W)) (ThetaInf (Sinf ψ W))) F
    from h _ o ho
  intro F o
  induction o generalizing F with
  | nil => intro _; rfl
  | cons j o ih =>
    intro hj
    simp only [List.foldl_cons]
    rw [ValZ.sigUpTo_eq Sig _ W E (hj j List.mem_cons_self)]
    exact ih _ fun j' hj' => hj j' (List.mem_cons_of_mem j hj')

/-- The value of a graph on two records that agree on `m`, on the waved kernels and on the chains
of the labels of its components. -/
private theorem ValZ_val_congr {k n : ℕ} (Γ : Graph k n) {D D' : ValZ.Rec d} (hm : D.m = D'.m)
    (hS : D.S = D'.S) (hSp : D.Sp = D'.Sp) (hSm : D.Sm = D'.Sm)
    (hch : ∀ c ∈ Γ.comps, ∀ o, c.kind = .theta o → D.chain o = D'.chain o)
    (e : Fin k → Fin d → ℤ) : ValZ.val Γ D e = ValZ.val Γ D' e := by
  unfold ValZ.val ValZ.term
  refine tsum_congr fun t => ?_
  rw [hm]
  congr 2
  refine List.map_congr_left fun c hc => ?_
  rcases c with ⟨κ, x, y, mi, lab⟩
  unfold ValZ.compVal
  cases κ with
  | waved w => cases w <;> simp only [hS, hSp, hSm]
  | theta o => simp only [hch _ hc o rfl]
  | _ => rfl

/-- `Σ^{(r),∞}_l(0, x)` is the value of `Sig l` on the record of [I, Def 7.1] at `S_∞ = Sinf ψ W`
whose label kernels are `Σ̊^∞ = ValZ.sigKer Sig ψ E`, when the labels of the graphs of `Sig l`
have entries `≤ l − 1` (as for the shape of an `l`-th order self-energy). -/
theorem ValZ.sigR_eq (Sig : ℕ → Expansion 2) (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ)
    (W : ℕ) (E : ℝ) {l : ℕ} (hl : 1 ≤ l)
    (hdet : ∀ g ∈ Sig l, g.2.comps.all (Comp.isDetKind (l - 1)) = true) (x : Fin d → ℤ) :
    ValZ.sigR Sig (Sinf ψ W) W E l x =
      ValZ.expVal (Sig l) (ValZ.rec (Sinf ψ W) (ValZ.sigKer Sig ψ E) W E) ![0, x] := by
  unfold ValZ.sigR ValZ.expVal
  congr 1
  refine List.map_congr_left fun g hg => ValZ_val_congr g.2
    (D := ValZ.rec (Sinf ψ W) (fun l' _ => ValZ.sigUpTo Sig (Sinf ψ W) W E l l') W E)
    (D' := ValZ.rec (Sinf ψ W) (ValZ.sigKer Sig ψ E) W E) rfl rfl rfl rfl
    (fun c hc o ho => ?_) _
  have h := List.all_eq_true.1 (hdet g hg) c hc
  simp only [Comp.isDetKind, ho, Bool.and_eq_true] at h
  have hlab := h.2
  simp only [labelOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hlab
  exact ValZ.chain_sigR Sig ψ W E l o fun j hj => by have := (hlab j hj).1.2; omega

/-! ## The shape conditions of a profile -/

section Instances

open Graphs

/-- The shape conditions of a profile. -/
private theorem ValZ_shape {d : ℕ} (P : Profile d) : ProfileShape P.ψ P.cψ :=
  ⟨P.cψ_pos, P.at_zero, P.le_max, P.symm⟩

end Instances

end RBM8D
