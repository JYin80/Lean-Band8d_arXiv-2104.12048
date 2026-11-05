import RBM8D.Graph.Syntax
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Values of atomic graphs

The value of a graph on a data record ([I, Def 2.9] = [II, Def 2.4]), the conditional expectation families `PFamily` (the operators P_x, Q_x of [I, §1.4]) and the value of a labelled graph, a random variable.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs
/-! ## Values -/

/-- The data a value reads ([I, Def 2.6, Def 6.3]; [II, §4.4, (6.3), Def 9.4]), over a finite
index type `ι`: `m`; the minors `Gm T = G^{(T)}` of the resolvent (`Gm ∅ = G`); `S`, `S⁺`, `S⁻`;
`Θ`; the self-energy matrices `Sig o = Σ_o` of labelled `Θ` edges; `Θ^{(n)}_err`; the ghost
factor `W²/L²`; auxiliary matrices. The relations between the fields are properties of the
random band matrix model, not of this record. -/
structure Data (ι : Type*) where
  m : ℂ
  Gm : Finset ι → Matrix ι ι ℂ
  S : Matrix ι ι ℂ
  Sp : Matrix ι ι ℂ
  Sm : Matrix ι ι ℂ
  Theta : Matrix ι ι ℂ
  Sig : ℕ → Matrix ι ι ℂ
  ThetaErr : ℕ → ℕ → Matrix ι ι ℂ
  ghost : ℂ
  aux : ℕ → Matrix ι ι ℂ

/-- The chain `Θ Σ_{o₁} Θ ⋯ Σ_{o_l} Θ` of [I, (6.11)] = [II, (2.10)]. -/
def Data.chain {ι : Type*} [Fintype ι] (D : Data ι) (o : List ℕ) : Matrix ι ι ℂ :=
  o.foldl (fun M l => M * D.Sig l * D.Theta) D.Theta

/-- The charge applied to a complex number: identity for `plus`, conjugation for `minus`. -/
def Charge.apply : Charge → ℂ → ℂ
  | .plus, z => z
  | .minus, z => star z

/-- The factor of one component at the labelling `σ` of the atoms. -/
def Comp.val {ι V : Type*} [Fintype ι] [DecidableEq ι] (D : Data ι) (σ : V → ι)
    (c : Comp V) : ℂ :=
  let g : Matrix ι ι ℂ := D.Gm (c.minor.map σ).toFinset
  let a := σ c.x
  let b := σ c.y
  match c.kind with
  | .G ch => ch.apply (g a b)
  | .weight ch => ch.apply (g a a)
  | .light ch => ch.apply (g a a - D.m)
  | .inv ch => ch.apply (g a a)⁻¹
  | .wD ch d =>
      ch.apply ((g a a)⁻¹ - D.m⁻¹ * ∑ j ∈ Finset.range (d + 1), (-(g a a - D.m) / D.m) ^ j)
  | .waved .s => D.S a b
  | .waved .plus => D.Sp a b
  | .waved .minus => D.Sm a b
  | .theta o => D.chain o a b
  | .thetaErr n d => D.ThetaErr n d a b
  | .ghost => D.ghost
  | .aux j _ _ => D.aux j a b
  | .dot => if a = b then 1 else 0
  | .xdot => if a = b then 0 else 1

/-- The product of the coefficient and of all component factors at the labelling `σ`. -/
def Graph.term {k n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Graph k n) (D : Data ι)
    (σ : Atom k n → ι) : ℂ :=
  Γ.coeff.eval D.m * (Γ.comps.map (Comp.val D σ)).prod

/-- The value of a graph read without its `P`/`Q` labels ([I, Def 2.9] for a graph without
labels): the sum over the labels `s` of the internal atoms of `term`, the external atoms being
labelled by `e`. -/
def Graph.val {k n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Graph k n) (D : Data ι)
    (e : Fin k → ι) : ℂ :=
  ∑ s : Fin n → ι, Γ.term D (Sum.elim e s)

/-- The value of a formal sum without labels: the sum of the values of its terms. -/
def Expansion.val {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Expansion k)
    (D : Data ι) (e : Fin k → ι) : ℂ :=
  (E.map fun g => g.2.val D e).sum

/-- A family of conditional expectations `P_x`, `x ∈ ι`, on random variables `Ω → ℂ`
([I, §1.4]: `P_x` is the expectation over the `x`-th row and column of `H`). -/
structure PFamily (Ω ι : Type*) where
  P : ι → (Ω → ℂ) → Ω → ℂ

/-- The operator of a label: `P_x`, or `Q_x = 1 - P_x`. -/
def PFamily.op {Ω ι : Type*} (PF : PFamily Ω ι) : PQ → ι → (Ω → ℂ) → Ω → ℂ
  | .P, x, f => PF.P x f
  | .Q, x, f => f - PF.P x f

/-- The laws of [I, §1.4] that the expansions use, on a class `Good` of random variables
(closed under sums, products, constants and `P_x`), for an expectation `E` and the predicate
`Meas x f` ("`f` does not depend on the `x`-th row and column of `H`"): linearity of `P_x`;
`P_x f = f` and the pull-out rule `P_x (f g) = f P_x g` for such `f`; `P_x f` and the constants
are such `f`; `E ∘ P_x = E`; `E` is additive. All identities hold at every `ω`. -/
structure PFamily.Laws {Ω ι : Type*} (PF : PFamily Ω ι) (E : (Ω → ℂ) → ℂ)
    (Meas : ι → (Ω → ℂ) → Prop) (Good : (Ω → ℂ) → Prop) : Prop where
  good_add : ∀ f g, Good f → Good g → Good (f + g)
  good_mul : ∀ f g, Good f → Good g → Good (f * g)
  good_const : ∀ a : ℂ, Good fun _ => a
  good_P : ∀ x f, Good f → Good (PF.P x f)
  add : ∀ x f g, Good f → Good g → PF.P x (f + g) = PF.P x f + PF.P x g
  smul : ∀ x (a : ℂ) f, Good f → PF.P x (a • f) = a • PF.P x f
  of_meas : ∀ x f, Good f → Meas x f → PF.P x f = f
  mul_left : ∀ x f g, Good f → Good g → Meas x f → PF.P x (f * g) = f * PF.P x g
  meas_P : ∀ x f, Good f → Meas x (PF.P x f)
  meas_const : ∀ x (a : ℂ), Meas x fun _ => a
  E_P : ∀ x f, Good f → E (PF.P x f) = E f
  E_add : ∀ f g, Good f → Good g → E (f + g) = E f + E g

/-- The distinct labels `(P or Q, u)` of a graph. -/
def Graph.labels {k n : ℕ} (Γ : Graph k n) : List (PQ × Atom k n) :=
  (Γ.comps.filterMap Comp.label).dedup

/-- The term of a labelled graph at the labelling `σ`, as a function of `ω`: the coefficient,
the unlabelled factors, and for every label `(pq, u)` the operator `P_{σ u}` or `Q_{σ u}` applied
to the product of the factors with that label ([I, Def 2.9]). -/
def Graph.termR {k n : ℕ} {Ω ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Graph k n)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (σ : Atom k n → ι) (ω : Ω) : ℂ :=
  Γ.coeff.eval (D ω).m *
    ((Γ.comps.filter fun c => c.label.isNone).map (Comp.val (D ω) σ)).prod *
    (Γ.labels.map fun ℓ =>
      PF.op ℓ.1 (σ ℓ.2)
        (fun ω' => ((Γ.comps.filter fun c => decide (c.label = some ℓ)).map
          (Comp.val (D ω') σ)).prod) ω).prod

/-- The value of a graph with `P`/`Q` labels ([I, Def 2.9] = [II, Def 2.4]), a random
variable: the sum of `termR` over the labels of the internal atoms. -/
def Graph.valR {k n : ℕ} {Ω ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Graph k n)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) : Ω → ℂ :=
  fun ω => ∑ s : Fin n → ι, Γ.termR PF D (Sum.elim e s) ω

/-- The value of a formal sum of labelled graphs. -/
def Expansion.valR {k : ℕ} {Ω ι : Type*} [Fintype ι] [DecidableEq ι] (E : Expansion k)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (e : Fin k → ι) : Ω → ℂ :=
  fun ω => (E.map fun g => g.2.valR PF D e ω).sum

/-- A map from graphs to formal sums preserves values on the data records and conditional
expectation families allowed by `Adm` (the form of the value identities of the local
expansions of [I, §3] = [II, §4]). -/
def PreservesValue {k n : ℕ} (O : Graph k n → Expansion k)
    (Adm : ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι], PFamily Ω ι → (Ω → Data ι) → Prop) :
    Prop :=
  ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι),
    Adm Ω ι PF D → ∀ (Γ : Graph k n) (e : Fin k → ι), (O Γ).valR PF D e = Γ.valR PF D e

section Instances

open Complex

end Instances

end RBM8D.Graphs
