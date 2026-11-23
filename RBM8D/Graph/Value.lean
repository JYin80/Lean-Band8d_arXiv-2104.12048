module

public import RBM8D.MainDefs
public import RBM8D.Graph.Syntax
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation

@[expose] public section

/-!
# Values of atomic graphs

The value of a graph on a data record ([I, Def 2.9] = [II, Def 2.4]), the conditional expectation families `PFamily` (the operators P_x, Q_x of [I, §1.4]) and the value of a labelled graph, a random variable.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs
/-! ## Values -/

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
