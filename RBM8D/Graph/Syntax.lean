import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Atomic graphs: syntax

The syntax of atomic graphs of [I, Def 2.6] = [II, Def 2.2] (with the later kinds of [II, §4.4, (4.21), (6.3), Def 9.4]): atoms, component kinds, components, coefficients, graphs and formal sums. No type here depends on the dimension, the band width or the side length.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs
/-! ## Syntax -/

/-- The atoms of a graph with `k` external atoms and `n` internal atoms ([I, Def 2.6]). -/
abbrev Atom (k n : ℕ) : Type := Fin k ⊕ Fin n

/-- The charge of a solid edge or weight: `plus` for a `G` factor, `minus` for a `Ḡ` factor. -/
inductive Charge
  | plus
  | minus
  deriving DecidableEq, Repr

/-- The waved edges of [I, Def 2.6]: neutral `s_{xy}`, positive `S⁺_{xy}`, negative `S⁻_{xy}`. -/
inductive Wave
  | s
  | plus
  | minus
  deriving DecidableEq, Repr

/-- The two label kinds `P_x` and `Q_x` of [I, Def 2.6]. -/
inductive PQ
  | P
  | Q
  deriving DecidableEq, Repr

/-- The kinds of graph components.

* `G c`: a solid edge, `G_{xy}` or `Ḡ_{xy}` ([I, Def 2.6]); with a nonempty minor set it is the
  entry `G^{(T)}_{xy}` of [II, §4.4].
* `weight c`, `light c`: the regular weight `G_{xx}` and the light weight `G_{xx} - m`.
* `inv c`: the weight `(G_{xx})⁻¹` of [II, §4.4].
* `wD c D`: the weight `W_D^{(x)} = (G_{xx})⁻¹ - m⁻¹ ∑_{j ≤ D} (-(G_{xx} - m)/m)^j` of [II, (4.21)].
* `waved w`: the waved edges `s`, `S⁺`, `S⁻`.
* `theta o`: the `Θ` edge with label `o = [o₁, …, o_l]`, of value `(Θ Σ_{o₁} Θ ⋯ Σ_{o_l} Θ)_{xy}`
  ([I, Def 6.3] = [II, Def 2.9]); `theta []` is the plain `Θ` edge.
* `thetaErr n D`: the edge `Θ^{(n)}_err` of [II, (6.3)].
* `ghost`: the ghost edge of [II, Def 9.4], a factor `W²/L²`.
* `aux j r b`: a further deterministic edge read from the `j`-th auxiliary matrix of the data
  record, of scaling order `r`, diffusive when `b` holds.
* `dot`, `xdot`: the dotted edge `1_{x = y}` and the `×`-dotted edge `1_{x ≠ y}`. -/
inductive Kind
  | G (c : Charge)
  | weight (c : Charge)
  | light (c : Charge)
  | inv (c : Charge)
  | wD (c : Charge) (D : ℕ)
  | waved (w : Wave)
  | theta (o : List ℕ)
  | thetaErr (n D : ℕ)
  | ghost
  | aux (j : ℕ) (r : ℤ) (b : Bool)
  | dot
  | xdot
  deriving DecidableEq, Repr

/-- A graph component on the atom type `V`: its kind, its two ends `x`, `y` (a weight sits on
`x`), the atoms `T` of a minor `G^{(T)}`, and an optional label `P_u` or `Q_u`. -/
structure Comp (V : Type*) where
  kind : Kind
  x : V
  y : V
  minor : List V
  label : Option (PQ × V)

/-- The image of a component under a map of the atoms. -/
def Comp.map {V W : Type*} (f : V → W) (c : Comp V) : Comp W :=
  ⟨c.kind, f c.x, f c.y, c.minor.map f, c.label.map (Prod.map id f)⟩

/-- The generators of the coefficient ring of [I, Def 2.6]: `m`, `m⁻¹`, `(1 - m²)⁻¹` and their
complex conjugates. -/
inductive CVar
  | m
  | mInv
  | r
  | mBar
  | mBarInv
  | rBar
  deriving DecidableEq, Repr

/-- The coefficients of [I, Def 2.6]: polynomials in the generators `CVar`. -/
abbrev Coeff : Type := MvPolynomial CVar ℂ

/-- The values of the generators at `m`. -/
def CVar.eval (m : ℂ) : CVar → ℂ
  | .m => m
  | .mInv => m⁻¹
  | .r => (1 - m ^ 2)⁻¹
  | .mBar => star m
  | .mBarInv => (star m)⁻¹
  | .rBar => (1 - star m ^ 2)⁻¹

/-- The value of a coefficient at `m`. -/
def Coeff.eval (m : ℂ) (p : Coeff) : ℂ := MvPolynomial.eval (CVar.eval m) p

/-- An atomic graph with `k` external and `n` internal atoms ([I, Def 2.6] = [II, Def 2.2]): a
list of components (a multigraph: parallel components stay distinct) and a coefficient. -/
structure Graph (k n : ℕ) where
  comps : List (Comp (Atom k n))
  coeff : Coeff

/-- A formal finite sum of graphs with `k` external atoms ([I, Def 2.9]); the terms may have
different numbers of internal atoms. -/
abbrev Expansion (k : ℕ) : Type := List (Σ n : ℕ, Graph k n)

/-- The image of a graph under a map of the atoms; a map that is not injective identifies
atoms, and a map may turn internal atoms into external ones and conversely ([I, Def 2.6]). -/
def Graph.mapAtoms {k n k' n' : ℕ} (Γ : Graph k n) (f : Atom k n → Atom k' n') : Graph k' n' :=
  ⟨Γ.comps.map (Comp.map f), Γ.coeff⟩

/-- The relabelling of the internal atoms by a permutation `π`. -/
def Graph.relabel {k n : ℕ} (Γ : Graph k n) (π : Equiv.Perm (Fin n)) : Graph k n :=
  Γ.mapAtoms (Sum.map id π)

/-- The graph `Γ` with its coefficient multiplied by `c`. -/
def Graph.smul {k n : ℕ} (c : Coeff) (Γ : Graph k n) : Graph k n := ⟨Γ.comps, c * Γ.coeff⟩

/-- A formal sum with every coefficient multiplied by `c`. -/
def Expansion.smul {k : ℕ} (c : Coeff) (E : Expansion k) : Expansion k :=
  E.map fun g => ⟨g.1, g.2.smul c⟩

/-- Weight kinds: the component sits on the atom `x`. -/
def Kind.isWeight : Kind → Bool
  | .weight _ | .light _ | .inv _ | .wD _ _ => true
  | _ => false

/-- Random kinds: the solid edges and all weights. -/
def Kind.isRandom : Kind → Bool
  | .G _ | .weight _ | .light _ | .inv _ | .wD _ _ => true
  | _ => false

/-- Well-formed components: a weight has `y = x`, and only solid edges and weights carry a
`P`/`Q` label ([I, Def 2.6]). -/
def Comp.WF {V : Type*} (c : Comp V) : Prop :=
  (c.kind.isWeight = true → c.y = c.x) ∧ (c.label.isSome = true → c.kind.isRandom = true)

/-- A graph without `P`/`Q` labels. -/
def Graph.LabelFree {k n : ℕ} (Γ : Graph k n) : Prop := ∀ c ∈ Γ.comps, c.label = none

/-- Kinds that join atoms into one molecule ([I, Def 3.4]): waved and dotted edges. -/
def Kind.joinsMol : Kind → Bool
  | .waved _ | .dot => true
  | _ => false

/-- Diffusive kinds ([I, Def 6.5, Def 7.5]): `Θ` edges with or without label, `Θ^{(n)}_err`,
and the auxiliary edges marked diffusive. -/
def Kind.isDiffusive : Kind → Bool
  | .theta _ | .thetaErr _ _ => true
  | .aux _ _ b => b
  | _ => false

/-- Kinds usable in a blue net besides the diffusive ones: blue solid edges `G` ([I, Def 6.5])
and ghost edges ([II, Def 9.4]). -/
def Kind.isBlue : Kind → Bool
  | .G .plus | .ghost => true
  | _ => false

/-- Solid edges. -/
def Kind.isSolid : Kind → Bool
  | .G _ => true
  | _ => false
end RBM8D.Graphs
