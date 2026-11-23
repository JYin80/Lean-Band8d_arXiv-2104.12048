module

public import Mathlib

@[expose] public section

/-!
# Delocalization and quantum diffusion of random band matrices in high dimensions

Statements of the main results of F. Yang, H.-T. Yau and J. Yin, *Delocalization and quantum
diffusion of random band matrices in high dimensions I: Self-energy renormalization*
(arXiv:2104.12048), proved together with part *II: T-expansion* (arXiv:2107.05795), with the
definitions they use. This file imports Mathlib and nothing else; the proofs are in the library
`RBM8D`, and `Solution.lean` connects each statement to the theorem of the library that proves it.

The three statements are the definitions `Thm13Stmt` ([I, Theorem 1.3]), `LocalLawStmt`
([I, Theorem 1.4]) and `quantumDiffusionStmt` ([I, Theorem 1.5] with [I, Corollaries 1.6, 1.7])
near the end of the definitions; they hold for every dimension `d ≥ 8` and have no hypotheses
other than their parameters. The graphs (`Graph`, `Expansion`) and their values enter only
through the self-energies `Σ_l` of [I, Theorem 1.5]. `docs/PAPER-VS-LEAN.md` reads each statement
in plain language and lists every difference from the printed ones.
-/

section
namespace RBM8D
/-- Distance from `u` to `0` on the cycle `ZMod L`. -/
def zdist (L : ℕ) (u : ZMod L) : ℕ := min u.val (L - u.val)

/-- The lattice `Z_L^d` of the paper. -/
abbrev Zd (d L : ℕ) : Type := Fin d → ZMod L

/-- The periodic `ℓ^∞` distance to the origin on `Z_L^d`, `‖x‖_L` of [I, (1.2)–(1.3)]. -/
def zdistInf (d L : ℕ) (x : Zd d L) : ℕ := Finset.univ.sup fun i => zdist L (x i)
end RBM8D
end
section
namespace RBM8D
open Complex
/-- A chosen square root of `z² - 4`. -/
noncomputable def mscDisc (z : ℂ) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (k := ℂ) (z ^ 2 - 4) (n := 2) Nat.zero_lt_two)

/-- The root `(-z + √(z² - 4)) / 2` of `m² + z m + 1 = 0`. -/
noncomputable def mscRoot₁ (z : ℂ) : ℂ := (-z + mscDisc z) / 2

/-- The root `(-z - √(z² - 4)) / 2` of `m² + z m + 1 = 0`. -/
noncomputable def mscRoot₂ (z : ℂ) : ℂ := (-z - mscDisc z) / 2

/-- The Stieltjes transform `m(z)` of the semicircle law, [I, (1.15)]: the root of
`m² + z m + 1 = 0` with positive imaginary part when `Im z > 0`. -/
noncomputable def msc (z : ℂ) : ℂ := if 0 < (mscRoot₁ z).im then mscRoot₁ z else mscRoot₂ z
end RBM8D
end
section
namespace RBM8D
open RCLike ComplexConjugate
open scoped ComplexInnerProductSpace
/-- The Green function `G(z) = (H - z)⁻¹`. -/
noncomputable def green {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (z : ℂ) :
    Matrix n n ℂ := (H - z • 1)⁻¹
end RBM8D
end
section
noncomputable section
open scoped BigOperators
namespace RBM8D.Graphs
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
  deriving Repr

/-- An injective code of a kind (the constructor and its arguments); it gives the decidable
equality of `Kind`. -/
def Kind.code : Kind → (ℕ × Charge × Wave) × (List ℕ × ℕ × ℕ) × (ℤ × Bool)
  | .G c => ((0, c, .s), ([], 0, 0), (0, false))
  | .weight c => ((1, c, .s), ([], 0, 0), (0, false))
  | .light c => ((2, c, .s), ([], 0, 0), (0, false))
  | .inv c => ((3, c, .s), ([], 0, 0), (0, false))
  | .wD c D => ((4, c, .s), ([], D, 0), (0, false))
  | .waved w => ((5, .plus, w), ([], 0, 0), (0, false))
  | .theta o => ((6, .plus, .s), (o, 0, 0), (0, false))
  | .thetaErr n D => ((7, .plus, .s), ([], n, D), (0, false))
  | .ghost => ((8, .plus, .s), ([], 0, 0), (0, false))
  | .aux j r b => ((9, .plus, .s), ([], j, 0), (r, b))
  | .dot => ((10, .plus, .s), ([], 0, 0), (0, false))
  | .xdot => ((11, .plus, .s), ([], 0, 0), (0, false))

theorem Kind.code_injective : Function.Injective Kind.code := by
  intro a b h
  cases a <;> cases b <;> simp_all [Kind.code]

instance instDecidableEqKind : DecidableEq Kind := Kind.code_injective.decidableEq

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
end
end
section
noncomputable section
open scoped BigOperators
namespace RBM8D.Graphs
/-- The scaling order of one component ([I, (2.12), (6.10)] = [II, (2.5), (2.11)];
[II, (4.21), (6.3), Def 9.4]): `1` for a solid edge and a light weight, `0` for regular and
`(-1)` weights, `D + 1` for `W_D`, `2` for a waved edge, `Σ oᵢ + 2 - 2l` for a `Θ` edge with
label `[o₁, …, o_l]` (`2` for the plain `Θ` edge), `2(D + 2)` for `Θ^{(n)}_err`, `0` for a
ghost edge, `2` for a dotted edge and `0` for a `×`-dotted edge. -/
def Kind.ord : Kind → ℤ
  | .G _ => 1
  | .weight _ => 0
  | .light _ => 1
  | .inv _ => 0
  | .wD _ d => (d : ℤ) + 1
  | .waved _ => 2
  | .theta o => (o.sum : ℤ) + 2 - 2 * o.length
  | .thetaErr _ d => 2 * ((d : ℤ) + 2)
  | .ghost => 0
  | .aux _ r _ => r
  | .dot => 2
  | .xdot => 0

/-- The scaling order of a graph ([I, Def 2.12, (6.10)] = [II, Def 2.6, (2.11)]): the sum of
the orders of its components minus twice the number of internal atoms. -/
def Graph.ord {k n : ℕ} (Γ : Graph k n) : ℤ :=
  (Γ.comps.map fun c => c.kind.ord).sum - 2 * n
end RBM8D.Graphs
end
end
section
noncomputable section
open scoped BigOperators
namespace RBM8D.Graphs
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
end RBM8D.Graphs
end
end
section
noncomputable section
open scoped BigOperators
namespace RBM8D.Graphs
/-- The graph on the atoms whose edges are the waved and dotted edges. -/
def Graph.molGraph {k n : ℕ} (Γ : Graph k n) : SimpleGraph (Atom k n) :=
  SimpleGraph.fromRel fun u v => ∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = u ∧ c.y = v

/-- Two atoms are in the same molecule ([I, Def 3.4] = [II, Def 2.10]): they are equal, or both
are internal and joined by a path of waved and dotted edges. Every external atom is a molecule
of its own. -/
def Graph.SameMol {k n : ℕ} (Γ : Graph k n) (u v : Atom k n) : Prop :=
  u = v ∨ (u.isRight = true ∧ v.isRight = true ∧ Γ.molGraph.Reachable u v)

/-- The graph on the internal atoms whose edges join two atoms of one molecule, or the two ends
of a component with index in `B`. Its connected components are the classes of internal molecules
joined by the edges of `B` in the molecular graph with the external molecules removed. -/
def Graph.net {k n : ℕ} (Γ : Graph k n) (B : Finset (Fin Γ.comps.length)) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b => Γ.SameMol (Sum.inr a) (Sum.inr b) ∨
    ∃ i ∈ B, (Γ.comps[i]'i.isLt).x = Sum.inr a ∧ (Γ.comps[i]'i.isLt).y = Sum.inr b

/-- The edges `B` contain a spanning tree of the internal molecules ([I, Def 6.5]): any two
internal atoms are joined in `net B`. -/
def Graph.Spans {k n : ℕ} (Γ : Graph k n) (B : Finset (Fin Γ.comps.length)) : Prop :=
  (Γ.net B).Preconnected

/-- The doubly connected property ([I, Def 6.5] = [II, Def 2.12], with [I, Def 7.5] and
[II, Def 9.4]): there are disjoint sets of components, a black net of diffusive edges and a blue
net of diffusive, blue solid or ghost edges, each containing a spanning tree of the molecular
graph with the external molecules removed. -/
def Graph.DoublyConnected {k n : ℕ} (Γ : Graph k n) : Prop :=
  ∃ black blue : Finset (Fin Γ.comps.length), Disjoint black blue ∧
    (∀ i ∈ black, (Γ.comps[i]'i.isLt).kind.isDiffusive = true) ∧
    (∀ i ∈ blue, (Γ.comps[i]'i.isLt).kind.isDiffusive = true ∨ (Γ.comps[i]'i.isLt).kind.isBlue = true) ∧
    Γ.Spans black ∧ Γ.Spans blue
end RBM8D.Graphs
end
end
section
noncomputable section
open scoped BigOperators
namespace RBM8D.Graphs
/-- The graph on the atoms whose edges are all components. -/
def Graph.edgeGraph {k n : ℕ} (Γ : Graph k n) : SimpleGraph (Atom k n) :=
  SimpleGraph.fromRel fun u v => ∃ c ∈ Γ.comps, c.x = u ∧ c.y = v

/-- The graph on the atoms whose edges are the waved and diffusive edges. -/
def Graph.wavedThetaGraph {k n : ℕ} (Γ : Graph k n) : SimpleGraph (Atom k n) :=
  SimpleGraph.fromRel fun u v => ∃ c ∈ Γ.comps,
    (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true) ∧ c.x = u ∧ c.y = v

/-- Regular graphs ([I, Def 2.11 (i)–(iii)] = [II, Def 2.5]), with the explicit bound `C` on
the numbers of atoms and components in place of "`O(1)`": connected; any two internal atoms
joined by a path of waved and `Θ` edges; no dotted edge between two internal atoms. -/
structure Graph.Regular {k n : ℕ} (C : ℕ) (Γ : Graph k n) : Prop where
  size : k + n + Γ.comps.length ≤ C
  connected : Γ.edgeGraph.Preconnected
  internal : ∀ a b : Fin n, Γ.wavedThetaGraph.Reachable (Sum.inr a) (Sum.inr b)
  noIntDot : ∀ c ∈ Γ.comps, c.kind = .dot → c.x.isLeft = true ∨ c.y.isLeft = true

/-- Normal regular graphs ([I, Def 2.11 (iv)] = [II, Def 2.5 (iv)]): every solid edge joins two
distinct atoms (the diagonal entries `G_{xx}` are weights), and two distinct atoms are joined by
a `×`-dotted edge if and only if they are joined by a solid edge. -/
def Graph.Normal {k n : ℕ} (C : ℕ) (Γ : Graph k n) : Prop :=
  Γ.Regular C ∧ (∀ c ∈ Γ.comps, c.kind.isSolid = true → c.x ≠ c.y) ∧ ∀ u v : Atom k n, u ≠ v →
    ((∃ c ∈ Γ.comps, c.kind = .xdot ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) ↔
      (∃ c ∈ Γ.comps, c.kind.isSolid = true ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)))
end RBM8D.Graphs
end
end
section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
universe u v w
namespace RBM8D
section Model
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
/-- An injective natural number key on a finite index type; it orients the off-diagonal pairs. -/
def idxKey (ι : Type u) [Fintype ι] (x : ι) : ℕ := (Fintype.equivFin ι x).val

/-- Off-diagonal pairs `(x, y)` with `idxKey x < idxKey y`: one per unordered pair `{x, y}`. -/
abbrev OffPair (ι : Type u) [Fintype ι] : Type u := {p : ι × ι // idxKey ι p.1 < idxKey ι p.2}

/-- Real coordinates of a Hermitian matrix: `h_xx` for each `x`, and `Re h_xy` (`true`),
`Im h_xy` (`false`) for each oriented off-diagonal pair. -/
abbrev Coord (ι : Type u) [Fintype ι] : Type u := ι ⊕ (OffPair ι × Bool)

/-- The sample space: one real number per coordinate. -/
abbrev Sample (ι : Type u) [Fintype ι] : Type u := Coord ι → ℝ

/-- Variance of a coordinate: `s_xx` on the diagonal, `s_xy / 2` for `Re h_xy` and `Im h_xy`
([I, Assumption 1.1], with a real diagonal of variance `s_xx`). -/
def coordVar (S : Matrix ι ι ℝ) : Coord ι → ℝ≥0
  | .inl x => (S x x).toNNReal
  | .inr (e, _) => (S e.1.1 e.1.2 / 2).toNNReal

/-- The law of [I, Assumption 1.1]: independent centred real Gaussians, one per coordinate. -/
def gaussLaw (S : Matrix ι ι ℝ) : Measure (Sample ι) :=
  Measure.pi fun c => gaussianReal 0 (coordVar S c)

/-- The Hermitian matrix `H(ω)`: `h_xy = Re + i Im` for `idxKey x < idxKey y`, `h_yx = conj h_xy`,
and `h_xx` real. -/
def hmat (ω : Sample ι) : Matrix ι ι ℂ :=
  Matrix.of fun x y =>
    if h : idxKey ι x < idxKey ι y then
      (ω (.inr (⟨(x, y), h⟩, true)) : ℂ) + I * (ω (.inr (⟨(x, y), h⟩, false)) : ℂ)
    else if h' : idxKey ι y < idxKey ι x then
      (ω (.inr (⟨(y, x), h'⟩, true)) : ℂ) - I * (ω (.inr (⟨(y, x), h'⟩, false)) : ℂ)
    else (ω (.inl x) : ℂ)
end Model
end RBM8D
end
end
section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
universe u v w
namespace RBM8D
/-- The window `adm(c₀, c₁) = {(W, L) | L^{c₁} ≤ W ≤ L^{1-c₀}}`. -/
def adm (c₀ c₁ : ℝ) : Set (ℕ × ℕ) :=
  {p | (p.2 : ℝ) ^ c₁ ≤ p.1 ∧ (p.1 : ℝ) ≤ (p.2 : ℝ) ^ (1 - c₀)}
end RBM8D
end
end
section
noncomputable section
open scoped BigOperators
namespace RBM8D.Graphs
/-- The atoms of a graph, externals first. -/
def allAtoms (k n : ℕ) : List (Atom k n) :=
  (List.finRange k).map Sum.inl ++ (List.finRange n).map Sum.inr

/-- The partition `P` with the blocks of `u` and `v` joined. -/
def joinBlocks {V : Type*} [DecidableEq V] (P : List (List V)) (u v : V) : List (List V) :=
  P.filter (fun B => !(B.contains u || B.contains v)) ++
    [(P.filter fun B => B.contains u || B.contains v).flatten]

/-- The partition of the atoms `as` into the classes of atoms joined by paths of dotted edges. -/
def dotBlocks {V : Type*} [DecidableEq V] (as : List V) (cs : List (Comp V)) : List (List V) :=
  cs.foldl (fun P c => if c.kind = .dot then joinBlocks P c.x c.y else P) (as.map fun a => [a])
end RBM8D.Graphs
end
end
section
noncomputable section
set_option linter.unusedVariables false
open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate
namespace RBM8D
variable {d L : ℕ}
/-- The character `x ↦ e^{i p·x}` of `Z_L^d` at the frequency `p = 2πk/L`. -/
def zchar [NeZero L] (k x : Zd d L) : ℂ := ∏ i, ZMod.stdAddChar (k i * x i)

/-- The frequency `p = 2πk/L ∈ T_L^d` of [I, (1.30)], with each `k_i` taken in `(−L/2, L/2]`
as in [I, (1.2)]. -/
def zfreq (k : Zd d L) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => 2 * Real.pi * ((k i).valMinAbs : ℝ) / L
end RBM8D
end
end
section
noncomputable section
set_option linter.unusedVariables false
open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate
namespace RBM8D
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The complexification of a real kernel. -/
def cmat (S : Matrix ι ι ℝ) : Matrix ι ι ℂ := S.map ((↑) : ℝ → ℂ)

/-- `Θ = |m|² S (1 − |m|² S)⁻¹`, [I, (1.16)]. -/
def Theta (m : ℂ) (S : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (‖m‖ ^ 2 • S) * Ring.inverse (1 - ‖m‖ ^ 2 • S)

/-- `S^+ = m² S (1 − m² S)⁻¹`, [I, (2.1)]. -/
def Splus (m : ℂ) (S : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  (m ^ 2 • cmat S) * Ring.inverse (1 - m ^ 2 • cmat S)

/-- `S^- = conj S^+`, [I, (2.1)]. -/
def Sminus (m : ℂ) (S : Matrix ι ι ℝ) : Matrix ι ι ℂ := (Splus m S).map (starRingEnd ℂ)
end RBM8D
end
end
section
noncomputable section
set_option linter.unusedVariables false
open Complex Matrix MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate
namespace RBM8D
variable {d L : ℕ}
/-- The symbol `K̂(p) = Σ_x K_{0x} e^{i p·x}` of a kernel on `Z_L^d` (display after [I, (1.30)]). -/
def symbol [NeZero L] (K : Matrix (Zd d L) (Zd d L) ℂ) (k : Zd d L) : ℂ :=
  ∑ x, K 0 x * zchar k x
end RBM8D
end
end
section
noncomputable section
set_option linter.unusedVariables false
open Complex MeasureTheory
open scoped FourierTransform SchwartzMap Nat ContDiff
namespace RBM8D
section Profile
variable {d : ℕ}
/-- The representative `[x]_L ∈ ((−L/2, L/2] ∩ ℤ)^d` of `x ∈ Z_L^d` ([I, (1.2)–(1.3)]), as a
point of `ℝ^d`. -/
def zrep {L : ℕ} (x : Zd d L) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => ((x i).valMinAbs : ℝ)

/-- The integral `(2π)^{−d} ∫ ψ(Wp) e^{i p·y} dp` of [I, (1.6)], before normalisation. -/
def profInt (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W : ℝ) (y : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ((2 * Real.pi : ℂ) ^ d)⁻¹ * ∫ p, (ψ (W • p) : ℂ) * cexp (I * (inner ℝ p y : ℝ))

/-- The unnormalised profile `x ↦ (2π)^{−d} ∫ ψ(Wp) e^{i p·[x]_L} dp` on `Z_L^d` ([I, (1.6)]). -/
def fRaw (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W L : ℕ) (x : Zd d L) : ℝ :=
  (profInt ψ W (zrep x)).re

/-- The normalisation `Z_{W,L}` of [I, (1.6)], chosen so that `Σ_x f_{W,L}(x) = 1`. -/
def ZWL (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W L : ℕ) [NeZero L] : ℝ :=
  ∑ x : Zd d L, fRaw ψ W L x

/-- The variance profile `f_{W,L}` of [I, (1.6)]. -/
def fWL (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W L : ℕ) [NeZero L] (x : Zd d L) : ℝ :=
  (ZWL ψ W L)⁻¹ * fRaw ψ W L x

/-- The variance matrix `S_{xy} = f_{W,L}([x − y]_L)` of [I, (1.5)]. -/
def Smat (ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (W L : ℕ) [NeZero L] :
    Matrix (Zd d L) (Zd d L) ℝ :=
  Matrix.of fun x y => fWL ψ W L (x - y)
end Profile
/-- [I, Assumption 1.2] with `f_{W,L} ≥ 0`: `ψ` is a real, symmetric Schwartz function with
`ψ(0) = 1`, `‖ψ‖_∞ ≤ 1`, `ψ(p) ≤ max(1 − c_ψ|p|², 1 − c_ψ)`; the function `f_{W,L}` of [I, (1.6)]
is nonnegative for every `W ≥ 1` and `L ≥ 1`, and symmetric on `Z_L^d` ([I, Assumption 1.1]) in
the regime `L ≫ W ≫ 1` of the model: for `(W, L) ∈ adm(c₀, c₁)` with `W ≥ W₀(c₀, c₁)`. -/
structure Profile (d : ℕ) where
  ψ : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)
  cψ : ℝ
  cψ_pos : 0 < cψ
  symm : ∀ p, ψ (-p) = ψ p
  at_zero : ψ 0 = 1
  abs_le_one : ∀ p, |ψ p| ≤ 1
  le_max : ∀ p, ψ p ≤ max (1 - cψ * ‖p‖ ^ 2) (1 - cψ)
  f_nonneg : ∀ (W L : ℕ) [NeZero L], 1 ≤ W → ∀ x : Zd d L, 0 ≤ fWL ψ W L x
  f_symm : ∀ c₀ c₁ : ℝ, 0 < c₀ → 0 < c₁ → ∃ W₀ : ℕ, ∀ (W L : ℕ) [NeZero L],
    (W, L) ∈ adm c₀ c₁ → W₀ ≤ W → ∀ x : Zd d L, fWL ψ W L (-x) = fWL ψ W L x
end RBM8D
end
end
section
noncomputable section
namespace RBM8D
/-- `B_{xy} = W^{-2} (‖x - y‖_L + W)^{-(d-2)}` of [I, (1.18)], with the periodic `ℓ^∞`
distance `‖·‖_L`. -/
def bB (d L W : ℕ) (x y : Zd d L) : ℝ :=
  (W : ℝ) ^ (-2 : ℝ) * ((zdistInf d L (x - y) : ℝ) + W) ^ (2 - (d : ℝ))

/-- The spectral domain `𝐃(κ, ε) = {E + iη : |E| < 2 - κ, W²/L^{2-ε} ≤ η ≤ 1}`. -/
def specDom (κ ε : ℝ) (W L : ℕ) : Set ℂ :=
  {z | |z.re| < 2 - κ ∧ (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) ≤ z.im ∧ z.im ≤ 1}
end RBM8D
end
end
section
namespace RBM8D.Graphs
/-- The dotted edges form a forest without loops: their number plus the number of dotted blocks
is the number of atoms. -/
def Graph.DotsAcyclic {k n : ℕ} (Γ : Graph k n) : Prop :=
  (Γ.comps.filter fun c => decide (c.kind = .dot)).length +
    (dotBlocks (allAtoms k n) Γ.comps).length = k + n
end RBM8D.Graphs
end
section
noncomputable section
open scoped BigOperators
namespace RBM8D.Graphs
/-- The deterministic data record at the variance matrix `S` and the spectral parameter `z`, with
self-energy matrices `Sig`: `m = m(z)`, `s = S`, `S^± = S^±(m)`, `Θ = Θ(m)` ([I, (1.16), (2.1)]);
the resolvent entries and the other fields are `0` (deterministic graphs do not read them). -/
def detData {ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (z : ℂ)
    (Sig : ℕ → Matrix ι ι ℂ) : Data ι where
  m := msc z
  Gm _ := 0
  S := cmat S
  Sp := Splus (msc z) S
  Sm := Sminus (msc z) S
  Theta := cmat (Theta (msc z) S)
  Sig := Sig
  ThetaErr _ _ := 0
  ghost := 0
  aux _ := 0

/-- The self-energy matrices of the family `Sig` below order `N`: the entry `k < N` is the value
of `Sig k` (external atoms `x = 0`, `y = 1`) on the deterministic record whose entries below `k`
are already computed; the entries `≥ N` are `0`. -/
def sigUpTo {ι : Type} [Fintype ι] [DecidableEq ι] (Sig : ℕ → Expansion 2) (S : Matrix ι ι ℝ)
    (z : ℂ) : ℕ → ℕ → Matrix ι ι ℂ
  | 0 => fun _ => 0
  | N + 1 => Function.update (sigUpTo Sig S z N) N
      (Matrix.of fun x y => (Sig N).val (detData S z (sigUpTo Sig S z N)) ![x, y])

/-- The matrix `(Σ_l)_{xy}`: the value of `Sig l` on the deterministic record with the self-energy
matrices of the lower orders. -/
def sigMat {ι : Type} [Fintype ι] [DecidableEq ι] (Sig : ℕ → Expansion 2) (S : Matrix ι ι ℝ)
    (z : ℂ) (l : ℕ) : Matrix ι ι ℂ :=
  Matrix.of fun x y => (Sig l).val (detData S z (sigUpTo Sig S z l)) ![x, y]

/-- The entries of a label of a labelled `Θ` edge ([II, Def 2.9]) are even and lie in `[4, N]`;
the empty label is the plain `Θ` edge. -/
def labelOK (N : ℕ) (o : List ℕ) : Bool :=
  o.all fun j => decide (4 ≤ j) && decide (j ≤ N) && j % 2 == 0

/-- The components of deterministic graphs built from `S`, `S^±`, `Θ` and labelled `Θ` edges
with labels of entries even in `[4, N]`: waved edges, `Θ` edges, dotted and `×`-dotted edges,
without minor and without label ([II, Def 2.7 (i)], [II, Def 3.3 (3)]). -/
def Comp.isDetKind {V : Type*} (N : ℕ) (c : Comp V) : Bool :=
  c.minor.isEmpty && c.label.isNone &&
    match c.kind with
    | .waved _ | .dot | .xdot => true
    | .theta o => labelOK N o
    | _ => false

/-- The shape of an `l`-th order self-energy ([II, Def 2.7 (i)], with [II, Def 3.2 (3)] and
[II, Def 3.3 (2), (3), (5)]): every graph of the formal sum (external atoms `x = 0`, `y = 1`) is
normal regular, and its dotted edges form a forest on the atoms (`Graph.DotsAcyclic`: no dotted
loop, at most one dotted edge between two atoms as in [I, Def 2.6] = [II, Def 2.2], and no
dotted cycle, so that every dotted edge counts `+2` in the scaling order of [I, (2.12)] against
one summation it removes); it is deterministic, of scaling order `l`, and its labelled `Θ` edges
carry labels with entries even in `[4, l - 1]`; it is doubly connected ([II, Def 2.12]) when its
external atoms `x`, `y` are read as internal atoms: the graph with the atoms `x, y` first and then
the internal atoms of `g`, all internal. A single dotted edge between `x` and `y` is allowed
([I, Def 2.13 (i)]). -/
def SelfEnergyShape (l : ℕ) (E : Expansion 2) : Prop :=
  ∀ g ∈ E, (∃ C, g.2.Normal C ∧ g.2.DotsAcyclic) ∧
    g.2.comps.all (Comp.isDetKind (l - 1)) = true ∧
    g.2.ord = l ∧
    (g.2.mapAtoms (Sum.elim (fun a => Sum.inr (Fin.castAdd g.1 a))
      (fun b => Sum.inr (Fin.natAdd 2 b))) : Graph 0 (2 + g.1)).DoublyConnected
end RBM8D.Graphs
end
end
section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
namespace RBM8D
section Entry
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- `G_{xy} − δ_{xy} m`. -/
def entryErr (G : Matrix ι ι ℂ) (m : ℂ) (x y : ι) : ℂ := G x y - if x = y then m else 0

/-- `T_{xy} = |m|² Σ_α s_{xα} |G_{αy}|²` ([I, (1.21)]). -/
def Tvar (S : Matrix ι ι ℝ) (G : Matrix ι ι ℂ) (m : ℂ) (x y : ι) : ℝ :=
  ‖m‖ ^ 2 * ∑ α, S x α * ‖G α y‖ ^ 2
end Entry
end RBM8D
end
end
section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
namespace RBM8D
/-- Sizes `(W, L)` with `L ≠ 0`: the parameter set of the model on `Z_L^d`. -/
abbrev SizeL : Type := {p : ℕ × ℕ // p.2 ≠ 0}

instance SizeL.neZero (p : SizeL) : NeZero p.1.2 := ⟨p.2⟩

/-- The law of [I, Assumption 1.1] on `Z_L^d` with the variance matrix `S_{xy} = f_{W,L}(x − y)`. -/
def rbmLaw (d : ℕ) (P : Profile d) (p : SizeL) : Measure (Sample (Zd d p.1.2)) :=
  gaussLaw (Smat P.ψ p.1.1 p.1.2)
end RBM8D
end
end
section
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Complex Matrix
open scoped ENNReal
namespace RBM8D
/-- **[I, Theorem 1.4], (1.19)**: for `d ≥ 8`, a profile `ψ`, constants `c₀, c₁, κ > 0` and all
`ε, τ, D > 0` there is `L₀` such that for `L ≥ L₀`, `L^{c₁} ≤ W ≤ L^{1−c₀}` and all `x, y`,
`P(∃ E ∈ (−2+κ, 2−κ), ∃ η ∈ [W²/L^{2−ε}, 1], |G_xy(E+iη) − m(E+iη) δ_xy|² > W^τ B_xy) ≤ L^{−D}`. -/
def LocalLawStmt : Prop :=
  ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ c₀ c₁ κ : ℝ, 0 < c₀ → 0 < c₁ → 0 < κ →
  ∀ ε τ D : ℝ, 0 < ε → 0 < τ → 0 < D →
  ∃ L₀ : ℕ, ∀ p : SizeL, L₀ ≤ p.1.2 → p.1 ∈ adm c₀ c₁ → ∀ x y : Zd d p.1.2,
    rbmLaw d P p {ω | ∃ E : ℝ, E ∈ Set.Ioo (-2 + κ) (2 - κ) ∧ ∃ η : ℝ,
        (p.1.1 : ℝ) ^ 2 / (p.1.2 : ℝ) ^ (2 - ε) ≤ η ∧ η ≤ 1 ∧
        (p.1.1 : ℝ) ^ τ * bB d p.1.2 p.1.1 x y <
          ‖entryErr (green (hmat ω) ((E : ℂ) + (η : ℂ) * I)) (msc ((E : ℂ) + (η : ℂ) * I)) x y‖ ^ 2}
      ≤ ENNReal.ofReal ((p.1.2 : ℝ) ^ (-D))

/-- `(u_α, λ_α)_α` is an orthonormal eigenbasis of `H`: `⟨u_α, u_β⟩ = δ_αβ` and `H u_α = λ_α u_α`;
the eigenvectors are indexed by the index set of `H` itself. -/
def IsOrthoEigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (u : ι → ι → ℂ) (lam : ι → ℝ) : Prop :=
  (∀ α β, ∑ x, star (u α x) * u β x = if α = β then 1 else 0) ∧
  ∀ α, H *ᵥ u α = (lam α : ℂ) • u α
open scoped Classical in
/-- The set `𝓑_{γ,K,ℓ}` of [I, §1.2]: bulk indices `α` (`λ_α ∈ (−2+κ, 2−κ)`) with
`min_{x₀} Σ_x |u_α(x)|² exp((‖x − x₀‖_L / ℓ)^γ) ≤ K`. -/
def locSetB (d L : ℕ) [NeZero L] (κ γ K ℓ : ℝ) (u : Zd d L → Zd d L → ℂ) (lam : Zd d L → ℝ) :
    Finset (Zd d L) :=
  Finset.univ.filter fun α => lam α ∈ Set.Ioo (-2 + κ) (2 - κ) ∧
    ∃ x₀ : Zd d L, ∑ x, ‖u α x‖ ^ 2 * Real.exp (((zdistInf d L (x - x₀) : ℝ) / ℓ) ^ γ) ≤ K
end RBM8D
end
end
section
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Complex Matrix
open scoped BigOperators
namespace RBM8D
open Graphs
/-- A family of matrices `Σ_l(W, L, z)` on `Z_L^d`, indexed by the order `l`, the band width `W`,
the side length `L` and the spectral parameter `z`. -/
abbrev SigmaFam (d : ℕ) : Type :=
  ℕ → ℕ → ∀ (L : ℕ) [NeZero L], ℂ → Matrix (Zd d L) (Zd d L) ℂ

/-- A family of matrices `𝒢(W, L, z)` on `Z_L^d`, indexed by `W`, `L` and `z`. -/
abbrev LocCorr (d : ℕ) : Type :=
  ℕ → ∀ (L : ℕ) [NeZero L], ℂ → Matrix (Zd d L) (Zd d L) ℂ

/-- The size `(W, L)` with `L ≠ 0`. -/
def sizeOf (W L : ℕ) [NeZero L] : SizeL := ⟨(W, L), NeZero.ne L⟩

/-- `E T_{xy}(z)` for `T_{xy} = |m|² Σ_α s_{xα} |G_{αy}|²` ([I, (1.21)]) under the law of
[I, Assumption 1.1] on `Z_L^d`. -/
def expT (d : ℕ) (P : Profile d) (W L : ℕ) [NeZero L] (z : ℂ) (x y : Zd d L) : ℝ :=
  ∫ ω, Tvar (Smat P.ψ W L) (green (hmat ω) z) (msc z) x y ∂(rbmLaw d P (sizeOf W L))

/-- `E |G_{xy}(z)|²` under the law of [I, Assumption 1.1] on `Z_L^d`. -/
def expG2 (d : ℕ) (P : Profile d) (W L : ℕ) [NeZero L] (z : ℂ) (x y : Zd d L) : ℝ :=
  ∫ ω, ‖green (hmat ω) z x y‖ ^ 2 ∂(rbmLaw d P (sizeOf W L))

/-- `|m(z)|²` as a complex number. -/
def mAbs2 (z : ℂ) : ℂ := ((‖msc z‖ ^ 2 : ℝ) : ℂ)

/-- `|m|² S` as a complex matrix. -/
def amat {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (z : ℂ) : Matrix ι ι ℂ :=
  mAbs2 z • cmat S

/-- The self-energy correction `Σ̃^{(M)} = Σ_{l=4}^{M} Σ_l` of [I, Theorem 1.5]. -/
def sigTildeM {d : ℕ} (Sg : SigmaFam d) (M W L : ℕ) [NeZero L] (z : ℂ) :
    Matrix (Zd d L) (Zd d L) ℂ :=
  ∑ l ∈ Finset.Icc 4 M, Sg l W L z

/-- The renormalized diffusive matrix `Θ^{(M)} = (1 − |m|² S X)⁻¹ |m|² S` of [I, (1.23)], with
`X = 1 + Σ̃^{(M)}`. -/
def thetaM {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (X : Matrix ι ι ℂ)
    (z : ℂ) : Matrix ι ι ℂ :=
  Ring.inverse (1 - amat S z * X) * amat S z

/-- The matrix `(1 − X |m|² S)⁻¹` of [I, (1.29)], with `X = 1 + Σ̃^{(M)}`. -/
def resM {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (X : Matrix ι ι ℂ)
    (z : ℂ) : Matrix ι ι ℂ :=
  Ring.inverse (1 - X * amat S z)

/-- `r(E) = √(4 − E²)/2` of [I, §1.3]. -/
def rE (E : ℝ) : ℝ := Real.sqrt (4 - E ^ 2) / 2

/-- The diffusion matrix `𝒟_{ij}(E) = (r(E)/2) Σ_x (x_i x_j / W²) s_{0x}` of [I, §1.3], with the
sum over `x ∈ Z_L^d` and `x_i ∈ (−L/2, L/2]`. -/
def diffD {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ) (W : ℕ) (E : ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => ((rE E / 2 * ∑ x : Zd d L,
    ((x i).valMinAbs : ℝ) * ((x j).valMinAbs : ℝ) / (W : ℝ) ^ 2 * S 0 x : ℝ) : ℂ)

/-- The matrix `(𝒟_l)_{ij} = W^{(l−2)d/2} (1/2) Σ_x (x_i x_j / W²) (Σ_l)_{0x}` of [I, §1.3], with
the sum over `x ∈ Z_L^d`. -/
def diffDl {d L : ℕ} [NeZero L] (K : Matrix (Zd d L) (Zd d L) ℂ) (W l : ℕ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => (((W : ℝ) ^ (((l : ℝ) - 2) * d / 2) / 2 : ℝ) : ℂ) * ∑ x : Zd d L,
    ((((x i).valMinAbs : ℝ) * ((x j).valMinAbs : ℝ) / (W : ℝ) ^ 2 : ℝ) : ℂ) * K 0 x

/-- `𝒟_eff^{(M)}(z) = 𝒟(E) + r(E) Σ_{l=4}^{M} W^{−(l−2)d/2} 𝒟_l(z)` of [I, §1.3], `E = Re z`. -/
def diffEff {d : ℕ} (P : Profile d) (Sg : SigmaFam d) (M W L : ℕ) [NeZero L] (z : ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  diffD (Smat P.ψ W L) W z.re + ((rE z.re : ℝ) : ℂ) • ∑ l ∈ Finset.Icc 4 M,
    (((W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) : ℝ) : ℂ) • diffDl (Sg l W L z) W l

/-- The quadratic form `W² p·𝒟 p` at the frequency `p = 2πk/L ∈ 𝕋_L^d`. -/
def qform {d L : ℕ} (W : ℕ) (k : Zd d L) (Dm : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  ((W : ℂ) ^ 2) * ∑ i, ∑ j, ((zfreq k i : ℝ) : ℂ) * Dm i j * ((zfreq k j : ℝ) : ℂ)

/-- The self-energies of [I, Theorem 1.5] (with [I, Def 2.13 (i)]): `Sig l` has the shape of an
`l`-th order self-energy for `l ≥ 4`; `Σ_l(W, L, z)` is the value of `Sig l` on the deterministic
record of `S_{W,L}` wherever `S_{W,L}` is symmetric; and [I, (1.25)] holds exactly for all
`W, L, z, x, a`. -/
def SigmaOf (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) (Sg : SigmaFam d) : Prop :=
  (∀ l, 4 ≤ l → SelfEnergyShape l (Sig l)) ∧
  (∀ l, 4 ≤ l → ∀ (W L : ℕ) [NeZero L] (z : ℂ), (Smat P.ψ W L).IsSymm →
    Sg l W L z = sigMat Sig (Smat P.ψ W L) z l) ∧
  (∀ l, 4 ≤ l → ∀ (W L : ℕ) [NeZero L] (z : ℂ) (x a : Zd d L),
    Sg l W L z x (x + a) = Sg l W L z 0 a ∧ Sg l W L z 0 a = Sg l W L z 0 (-a))

/-- The conclusions of [I, Theorem 1.5] and [I, Corollary 1.6] at order `M`: for every `τ > 0`
there is `L₀` such that for `L ≥ L₀`, `(W, L) ∈ adm(c₀, c₁)`, `z ∈ 𝐃(κ, ε)`:
`1 − |m|² S (1 + Σ̃^{(M)})` is invertible, (1.24), (1.26), (1.27) for `4 ≤ l ≤ M`, and (1.28);
and there are `C`, `L₀` with (1.22) and (1.29) for `L ≥ L₀`, `(W, L) ∈ adm(c₀, c₁)`,
`z ∈ 𝐃(κ, ε)` and all `x, y`. In (1.26) the diagonal term `L^τ W^{−(l−2)d/2} 1_{x=0}` is added:
`|Σ_l(0, x)| ≤ L^τ W^{−(l−4)d/2} B_{0x}² + L^τ W^{−(l−2)d/2} 1_{x=0}` (as in
`SelfEnergyBound`). -/
def thm15Concl (d : ℕ) (P : Profile d) (c₀ c₁ κ ε : ℝ) (Sg : SigmaFam d) (M : ℕ)
    (Gc : LocCorr d) : Prop :=
  (∀ τ : ℝ, 0 < τ → ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
    ∀ z ∈ specDom κ ε W L,
      IsUnit (1 - amat (Smat P.ψ W L) z * (1 + sigTildeM Sg M W L z)) ∧
      (∀ x y : Zd d L, ‖thetaM (Smat P.ψ W L) (1 + sigTildeM Sg M W L z) z x y‖ ≤
        (L : ℝ) ^ τ * bB d L W x y) ∧
      (∀ l, 4 ≤ l → l ≤ M → ∀ x : Zd d L, ‖Sg l W L z 0 x‖ ≤
        (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 4) * d / 2)) * bB d L W 0 x ^ 2 +
          (if x = 0 then (L : ℝ) ^ τ * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2)) else 0)) ∧
      (∀ l, 4 ≤ l → l ≤ M → ‖∑ x : Zd d L, Sg l W L z 0 x‖ ≤
        (L : ℝ) ^ τ * z.im * (W : ℝ) ^ (-(((l : ℝ) - 2) * d / 2))) ∧
      (∀ x y : Zd d L, ‖Gc W L z x y‖ ≤ (L : ℝ) ^ τ * bB d L W x y ^ ((3 : ℝ) / 2))) ∧
  (∃ C : ℝ, ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L → (W, L) ∈ adm c₀ c₁ →
    ∀ z ∈ specDom κ ε W L, ∀ x y : Zd d L,
      ‖(expT d P W L z x y : ℂ) - (thetaM (Smat P.ψ W L) (1 + sigTildeM Sg M W L z) z *
          (mAbs2 z • 1 + Gc W L z)) x y‖ ≤ C * (W : ℝ) ^ (-((M : ℝ) * d / 2)) ∧
      ‖(expG2 d P W L z x y : ℂ) - (resM (Smat P.ψ W L) (1 + sigTildeM Sg M W L z) z *
          (mAbs2 z • 1 + Gc W L z)) x y‖ ≤ C * (W : ℝ) ^ (-((M : ℝ) * d / 2)))

/-- The conclusions of [I, Corollary 1.7] at order `M` (quantified form): for all `δ, τ > 0`
there are `C`, `L₀` such that for `L ≥ L₀`, `(W, L) ∈ adm(c₀, c₁)` with `W^M ≥ L⁴`,
`|E| < 2 − κ`, `η ∈ [W²/L^{2−ε}, W^{−δ}]` and `p = 2πk/L` with `|p| ≤ W^{−1−δ}`, at `z = E + iη`:
(1.35) `Σ_x E T_{0x} e^{ip·x} = Θ̂^{(M)}(p)(|m|² + e₁) + e₃`, and (1.36)
`Σ_x E|G_{0x}|² e^{ip·x} = r(E)(|m|² + e₁)/(η + W² p·𝒟_eff^{(M)} p + e₂) + e₃` with a nonzero
denominator, where `|e₁| ≤ C W^{−d/2+τ}`, `|e₂| ≤ C(η² + W^{−d+τ}η + W³|p|³)`,
`|e₃| ≤ C W^{−M}`. -/
def cor17Concl (d : ℕ) (P : Profile d) (c₀ c₁ κ ε : ℝ) (Sg : SigmaFam d) (M : ℕ) : Prop :=
  ∀ δ τ : ℝ, 0 < δ → 0 < τ → ∃ C : ℝ, ∃ L₀ : ℕ, ∀ (W L : ℕ) [NeZero L], L₀ ≤ L →
    (W, L) ∈ adm c₀ c₁ → (L : ℝ) ^ 4 ≤ (W : ℝ) ^ M →
    ∀ E η : ℝ, |E| < 2 - κ → (W : ℝ) ^ 2 / (L : ℝ) ^ (2 - ε) ≤ η → η ≤ (W : ℝ) ^ (-δ) →
    ∀ k : Zd d L, ‖zfreq k‖ ≤ (W : ℝ) ^ (-1 - δ) →
      (∃ e₁ e₃ : ℂ, ‖e₁‖ ≤ C * (W : ℝ) ^ (-((d : ℝ) / 2) + τ) ∧
        ‖e₃‖ ≤ C * (W : ℝ) ^ (-(M : ℝ)) ∧
        ∑ x : Zd d L, zchar k x * (expT d P W L (E + η * I) 0 x : ℂ) =
          symbol (thetaM (Smat P.ψ W L) (1 + sigTildeM Sg M W L (E + η * I)) (E + η * I)) k *
            (mAbs2 (E + η * I) + e₁) + e₃) ∧
      (∃ e₁ e₂ e₃ : ℂ, ‖e₁‖ ≤ C * (W : ℝ) ^ (-((d : ℝ) / 2) + τ) ∧
        ‖e₂‖ ≤ C * (η ^ 2 + (W : ℝ) ^ (-(d : ℝ) + τ) * η + (W : ℝ) ^ 3 * ‖zfreq k‖ ^ 3) ∧
        ‖e₃‖ ≤ C * (W : ℝ) ^ (-(M : ℝ)) ∧
        (η : ℂ) + qform W k (diffEff P Sg M W L (E + η * I)) + e₂ ≠ 0 ∧
        ∑ x : Zd d L, zchar k x * (expG2 d P W L (E + η * I) 0 x : ℂ) =
          (rE E : ℂ) * (mAbs2 (E + η * I) + e₁) /
            ((η : ℂ) + qform W k (diffEff P Sg M W L (E + η * I)) + e₂) + e₃)

/-- **[I, Theorem 1.5] + [I, Corollary 1.6] + [I, Corollary 1.7]** (joint): for `d ≥ 8`, a
profile `P` and constants `c₀, c₁, κ, ε > 0` there is one family of self-energies `Σ_l`
(before `M`), and for every order `M` a local correction `𝒢^{(M)}`, such that the conclusions of
[I, Theorem 1.5] and [I, Corollary 1.6] (`thm15Concl`) and of [I, Corollary 1.7]
(`cor17Concl`) hold. -/
def quantumDiffusionStmt : Prop :=
  ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ c₀ c₁ κ ε : ℝ, 0 < c₀ → 0 < c₁ → 0 < κ → 0 < ε →
    ∃ Sg : SigmaFam d, (∃ Sig : ℕ → Expansion 2, SigmaOf d P Sig Sg) ∧
      ∀ M : ℕ, ∃ Gc : LocCorr d,
        thm15Concl d P c₀ c₁ κ ε Sg M Gc ∧ cor17Concl d P c₀ c₁ κ ε Sg M
end RBM8D
end
end
section
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Complex Matrix
open scoped ENNReal
namespace RBM8D
open Graphs
/-- **[I, Theorem 1.3]**, (1.12) and (1.13) jointly: for `d ≥ 8`, `ψ`, `c₀, c₁, κ > 0`,
`γ ∈ (0, 1]`, `K > 1` and all `τ, D > 0` there is one `L₀` such that for `L ≥ L₀`,
`W ≤ ℓ ≤ L^{1−c₀}` and `L^{c₁} ≤ W ≤ L`,
`P(∃ (u, λ) orthonormal eigenbasis of H, |𝓑_{γ,K,ℓ}| / N > W^τ (ℓ²/L² + W^{−d/2})) ≤ L^{−D}` and
`P(∃ λ ∈ (−2+κ, 2−κ), ∃ u, ‖u‖₂ = 1, H u = λ u, ‖u‖_∞ > W^{1+τ}/L) ≤ L^{−D}`. -/
def Thm13Stmt : Prop :=
  ∀ d : ℕ, 8 ≤ d → ∀ P : Profile d, ∀ c₀ c₁ κ : ℝ, 0 < c₀ → 0 < c₁ → 0 < κ →
  ∀ γ K : ℝ, 0 < γ → γ ≤ 1 → 1 < K → ∀ τ D : ℝ, 0 < τ → 0 < D →
  ∃ L₀ : ℕ, ∀ (p : SizeL) (ℓ : ℝ), L₀ ≤ p.1.2 → (p.1.1 : ℝ) ≤ ℓ → ℓ ≤ (p.1.2 : ℝ) ^ (1 - c₀) →
    (p.1.2 : ℝ) ^ c₁ ≤ p.1.1 → p.1.1 ≤ p.1.2 →
    rbmLaw d P p {ω | ∃ (u : Zd d p.1.2 → Zd d p.1.2 → ℂ) (lam : Zd d p.1.2 → ℝ),
        IsOrthoEigenbasis (hmat ω) u lam ∧
        (p.1.1 : ℝ) ^ τ * (ℓ ^ 2 / (p.1.2 : ℝ) ^ 2 + (p.1.1 : ℝ) ^ (-(d : ℝ) / 2)) <
          ((locSetB d p.1.2 κ γ K ℓ u lam).card : ℝ) / (p.1.2 : ℝ) ^ d}
      ≤ ENNReal.ofReal ((p.1.2 : ℝ) ^ (-D)) ∧
    rbmLaw d P p {ω | ∃ lam : ℝ, lam ∈ Set.Ioo (-2 + κ) (2 - κ) ∧ ∃ u : Zd d p.1.2 → ℂ,
        ∑ x, ‖u x‖ ^ 2 = 1 ∧ hmat ω *ᵥ u = (lam : ℂ) • u ∧
        ∃ x, (p.1.1 : ℝ) ^ (1 + τ) / (p.1.2 : ℝ) < ‖u x‖}
      ≤ ENNReal.ofReal ((p.1.2 : ℝ) ^ (-D))
end RBM8D
end
end

/-! ## The statements -/

section
namespace RBM8D

/-- [I, Theorem 1.3]: weak delocalization of the bulk eigenvectors, (1.12) and (1.13); the statement is `Thm13Stmt`. -/
theorem theorem_1_3 : Thm13Stmt := by
  sorry

/-- [I, Theorem 1.4]: the local law (1.19); the statement is `LocalLawStmt`. -/
theorem theorem_1_4 : LocalLawStmt := by
  sorry

/-- [I, Theorem 1.5] with [I, Corollaries 1.6 and 1.7]: quantum diffusion; the statement is `quantumDiffusionStmt`. -/
theorem theorem_1_5 : quantumDiffusionStmt := by
  sorry

end RBM8D
end
