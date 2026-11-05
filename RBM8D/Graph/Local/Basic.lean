import RBM8D.Graph.Order
import RBM8D.Graph.Value
import RBM8D.Graph.Molecule
import RBM8D.Graph.Regular
import RBM8D.Basic.Minor
import RBM8D.Basic.Semicircle

/-!
# Local expansions: basic objects

Tracked formal sums, building blocks of the graph operations, partial derivatives of components ([I, (3.8)]), matched and mismatched edges, standard neutral atoms and locally standard graphs ([I, Defs 3.12, 3.17, 3.20] = [II, Defs 4.7, 4.8]), the model relations `ModelAdm`, and the graphs of [I, Lemma 2.5].
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-- A graph with `k` external atoms together with a map from the atoms of an input graph with
`n` internal atoms; atoms identified by a dotted edge have the same image. -/
structure Tracked (k n : ℕ) where
  nOut : ℕ
  g : Graph k nOut
  f : Atom k n → Atom k nOut

/-- A formal sum of tracked graphs. -/
abbrev TExpansion (k n : ℕ) : Type := List (Tracked k n)

/-- The formal sum, without the atom maps. -/
def TExpansion.forget {k n : ℕ} (E : TExpansion k n) : Expansion k :=
  E.map fun t => ⟨t.nOut, t.g⟩

/-- A graph with the identity map. -/
def Tracked.self {k n : ℕ} (Γ : Graph k n) : Tracked k n := ⟨n, Γ, id⟩

/-- The operator `O` applied to every graph of `E`, at the images of the input atoms; the atom
maps compose. -/
def TExpansion.bind {k n : ℕ} (E : TExpansion k n)
    (O : ∀ {n' : ℕ}, (Atom k n → Atom k n') → Graph k n' → TExpansion k n') :
    TExpansion k n :=
  E.flatMap fun t => (O t.f t.g).map fun s => ⟨s.nOut, s.g, s.f ∘ t.f⟩

/-- An atom of an output graph that is not the image of an input atom. -/
def Tracked.IsNew {k n : ℕ} (t : Tracked k n) (u : Atom k t.nOut) : Prop := ∀ v, t.f v ≠ u

/-- `E` has the value of `Γ` for every data record and conditional expectation family allowed
by `Adm`. -/
def TExpansion.ValueEq {k n : ℕ} (E : TExpansion k n) (Γ : Graph k n)
    (Adm : ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι], PFamily Ω ι → (Ω → Data ι) → Prop) :
    Prop :=
  ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι),
    Adm Ω ι PF D → ∀ e : Fin k → ι, E.forget.valR PF D e = Γ.valR PF D e

/-- The component of kind `κ` from `u` to `v`, without minor and without label. -/
def mkC {V : Type*} (κ : Kind) (u v : V) : Comp V := ⟨κ, u, v, [], none⟩

/-- The solid edge `G_{uv}` (charge `plus`) or `Ḡ_{uv}` (charge `minus`); the weight `G_{uu}`
or `Ḡ_{uu}` when `u = v`. -/
def solidC {V : Type*} [DecidableEq V] (ch : Charge) (u v : V) : Comp V :=
  if u = v then mkC (.weight ch) u u else mkC (.G ch) u v

/-- The component with the label `Q_u` if it is random, unchanged otherwise. -/
def Comp.labelQ {V : Type*} (u : V) (c : Comp V) : Comp V :=
  if c.kind.isRandom then { c with label := some (.Q, u) } else c

/-- All random components of a list labelled `Q_u`. -/
def labelQs {V : Type*} (u : V) (cs : List (Comp V)) : List (Comp V) := cs.map (Comp.labelQ u)

/-- The atom map of a graph with `j` more internal atoms: old atoms keep their indices. -/
def liftA {k n : ℕ} (j : ℕ) : Atom k n → Atom k (n + j) := Sum.map id (Fin.castAdd j)

/-- The components of a graph moved to a graph with `j` more internal atoms. -/
def liftCs {k n : ℕ} (j : ℕ) (cs : List (Comp (Atom k n))) : List (Comp (Atom k (n + j))) :=
  cs.map (Comp.map (liftA j))

/-- The `i`-th new internal atom of a graph with `j` more internal atoms. -/
def newA {k n j : ℕ} (i : Fin j) : Atom k (n + j) := Sum.inr (Fin.natAdd n i)

/-- The list without the entries at the indices `is`. -/
def eraseIdxs {α : Type*} (is : List ℕ) (l : List α) : List α :=
  (l.zipIdx.filter fun p => !is.contains p.2).map Prod.fst

/-- The coefficient `m` (charge `plus`) or `m̄` (charge `minus`). -/
def mOf : Charge → Coeff
  | .plus => MvPolynomial.X .m
  | .minus => MvPolynomial.X .mBar

/-- The coefficient `m`. -/
abbrev cm : Coeff := MvPolynomial.X .m

/-- The coefficient `m̄`. -/
abbrev cmb : Coeff := MvPolynomial.X .mBar

/-- The opposite charge. -/
def Charge.flip : Charge → Charge
  | .plus => .minus
  | .minus => .plus

/-- The kind of the complex conjugate component: solid edges and weights change charge, `S⁺`
and `S⁻` are exchanged, the other kinds are unchanged. -/
def Kind.conj : Kind → Kind
  | .G c => .G c.flip
  | .weight c => .weight c.flip
  | .light c => .light c.flip
  | .inv c => .inv c.flip
  | .wD c d => .wD c.flip d
  | .waved .plus => .waved .minus
  | .waved .minus => .waved .plus
  | κ => κ

/-- The generator of the coefficient ring of the complex conjugate value. -/
def CVar.conj : CVar → CVar
  | .m => .mBar
  | .mInv => .mBarInv
  | .r => .rBar
  | .mBar => .m
  | .mBarInv => .mInv
  | .rBar => .r

/-- The coefficient whose value at `m` is the complex conjugate of the value of `p`. -/
def Coeff.conj (p : Coeff) : Coeff :=
  MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.rename CVar.conj p)

/-- The complex conjugate graph `\overline{𝒢}` of [I, (3.6)]: the kinds of all components are
conjugated and the coefficient is conjugated. -/
def Graph.conj {k n : ℕ} (Γ : Graph k n) : Graph k n :=
  ⟨Γ.comps.map fun c => { c with kind := c.kind.conj }, Coeff.conj Γ.coeff⟩

/-- The complex conjugate of every graph of a tracked formal sum. -/
def TExpansion.conj {k n : ℕ} (E : TExpansion k n) : TExpansion k n :=
  E.map fun t => ⟨t.nOut, t.g.conj, t.f⟩

/-- A component without minor, without label, and not a `(G_{xx})⁻¹` or `W_D` weight. -/
def Comp.isPlainB {V : Type*} (c : Comp V) : Bool :=
  c.minor.isEmpty && c.label.isNone &&
    match c.kind with
    | .inv _ | .wD _ _ => false
    | _ => true

/-- Graphs without `G^{(T)}` entries, without `(G_{xx})⁻¹` or `W_D` weights (the graphs of
[II] outside §4.4), without a dotted loop `1_{u = u}`, and with every component well formed
(weights on their atom, labels on random components). -/
def Graph.Plain {k n : ℕ} (Γ : Graph k n) : Prop :=
  ∀ c ∈ Γ.comps, c.minor = [] ∧ (∀ ch, c.kind ≠ .inv ch) ∧ (∀ ch d, c.kind ≠ .wD ch d) ∧
    (c.kind = .dot → c.x ≠ c.y) ∧ c.WF

/-- A component with its atoms numbered, the external atoms first. -/
structure CompCode where
  kind : Kind
  x : ℕ
  y : ℕ
  minor : List ℕ
  label : Option (PQ × ℕ)
  deriving DecidableEq

/-- The code of a component. -/
def Comp.code {k n : ℕ} (c : Comp (Atom k n)) : CompCode :=
  let a : Atom k n → ℕ := Sum.elim (fun i => i.val) (fun i => k + i.val)
  ⟨c.kind, a c.x, a c.y, c.minor.map a, c.label.map (Prod.map id a)⟩

/-- The codes of the components of a graph. -/
def Graph.code {k n : ℕ} (Γ : Graph k n) : List CompCode := Γ.comps.map Comp.code

/-- The two factors of `-∂_{h_{pq}} c` for a random component `c` without minor:
`∂_{h_{pq}} G_{ab} = -G_{ap} G_{qb}` and `∂_{h_{pq}} Ḡ_{ab} = -Ḡ_{aq} Ḡ_{pb}` ([I, (3.8)]); a
weight or light weight on `a` is the case `b = a`. Deterministic components have no factors. -/
def Comp.dPieces {V : Type*} [DecidableEq V] (p q : V) (c : Comp V) : Option (List (Comp V)) :=
  let b := if c.kind.isWeight then c.x else c.y
  match c.kind with
  | .G .plus | .weight .plus | .light .plus => some [solidC .plus c.x p, solidC .plus q b]
  | .G .minus | .weight .minus | .light .minus => some [solidC .minus c.x q, solidC .minus p b]
  | _ => none

/-- The product rule for `-∂_{h_{pq}}` of the product of the components `cs`: one list per random
component, that component replaced by its two factors. -/
def dTerms {V : Type*} [DecidableEq V] (p q : V) (cs : List (Comp V)) : List (List (Comp V)) :=
  (List.finRange cs.length).filterMap fun i =>
    (cs[i].dPieces p q).map fun ps => cs.eraseIdx i ++ ps

/-- The number of solid edges attached to `u` ([I, (3.9)]). -/
def Graph.deg {k n : ℕ} (Γ : Graph k n) (u : Atom k n) : ℕ :=
  (Γ.comps.filter fun c => c.kind.isSolid && (c.x == u || c.y == u)).length

/-- The ends at `x` of the solid edges attached to `x` (self-loops excluded): whether the edge
leaves `x` (`true`) or enters `x` (`false`), and its charge. The edge `G_{uv}` is drawn as an
arrow from `u` to `v`. -/
def Graph.ends {k n : ℕ} (Γ : Graph k n) (x : Atom k n) : List (Bool × Charge) :=
  Γ.comps.filterMap fun c =>
    match c.kind with
    | .G ch => if c.x = x ∧ c.y ≠ x then some (true, ch)
        else if c.y = x ∧ c.x ≠ x then some (false, ch) else none
    | _ => none

/-- Two solid edges at an atom are matched (the four panels of the figure `match` of
[I, Def 3.12] = [II, Def 4.7]): they have the same charge and one enters while the other leaves,
or they have opposite charges and both enter or both leave. The six other configurations (the
panels of the figure `mismatch`) are mismatched. -/
def matchedEnds (e₁ e₂ : Bool × Charge) : Bool :=
  (e₁.2 == e₂.2 && e₁.1 != e₂.1) || (e₁.2 != e₂.2 && e₁.1 == e₂.1)

/-- The atom `x` has exactly two solid edges and they are matched. -/
def Graph.matchedAt {k n : ℕ} (Γ : Graph k n) (x : Atom k n) : Bool :=
  Γ.deg x == 2 &&
    match Γ.ends x with
    | [e₁, e₂] => matchedEnds e₁ e₂
    | _ => false

/-- The atom `x` has exactly two solid edges and they are mismatched. -/
def Graph.mismatchedAt {k n : ℕ} (Γ : Graph k n) (x : Atom k n) : Bool :=
  Γ.deg x == 2 &&
    match Γ.ends x with
    | [e₁, e₂] => !matchedEnds e₁ e₂
    | _ => false

/-- Standard neutral atoms ([I, Def 3.17] = [II, Def 4.7]): besides `×`-dotted edges, exactly
three components are attached to `x`: two matched solid edges of opposite charges and one
neutral waved edge `s`. -/
def Graph.stdNeutralAt {k n : ℕ} (Γ : Graph k n) (x : Atom k n) : Bool :=
  let cs := Γ.comps.filter fun c => c.kind != .xdot && (c.x == x || c.y == x)
  cs.length == 3 && (cs.filter fun c => c.kind.isSolid).length == 2 &&
    (cs.filter fun c => c.kind == .waved .s).length == 1 &&
    match Γ.ends x with
    | [e₁, e₂] => matchedEnds e₁ e₂ && e₁.2 != e₂.2
    | _ => false

/-- The number of regular and light weights on `u`. -/
def Graph.wt {k n : ℕ} (Γ : Graph k n) (u : Atom k n) : ℕ :=
  (Γ.comps.filter fun c => (c.kind matches .weight _ | .light _) && c.x == u).length

/-- Locally standard graphs ([I, Def 3.20] = [II, Def 4.8]), normality apart: no `P`/`Q` labels;
no weights of any kind on any atom; every internal atom has degree `0` or `2`; every internal atom
of degree `2` is standard neutral. -/
def Graph.LocallyStandard {k n : ℕ} (Γ : Graph k n) : Prop :=
  Γ.LabelFree ∧ (∀ c ∈ Γ.comps, c.kind.isWeight = false) ∧
    ∀ i : Fin n, (Γ.deg (.inr i) = 0 ∨ Γ.deg (.inr i) = 2) ∧
      (Γ.deg (.inr i) = 2 → Γ.stdNeutralAt (.inr i) = true)

/-- `Q`-graphs with the label `Q_u` ([I, Def 2.14 (ii)] for a given atom `u`). -/
def Graph.IsQGraphAt {k n : ℕ} (Γ : Graph k n) (u : Atom k n) : Prop :=
  (∃ c ∈ Γ.comps, c.label = some (.Q, u)) ∧
    ∀ c ∈ Γ.comps, (c.kind.isRandom = true ∨ c.label.isSome = true) → c.label = some (.Q, u)

/-- Graphs `Γ₀ Q_u(Γ̃₀)` of [II, (4.16)]: every label is `Q_u` and some component carries it; the
unlabelled components form `Γ₀`, the labelled ones `Γ̃₀`. -/
def Graph.IsQFormAt {k n : ℕ} (Γ : Graph k n) (u : Atom k n) : Prop :=
  (∃ c ∈ Γ.comps, c.label = some (.Q, u)) ∧ ∀ c ∈ Γ.comps, c.label = none ∨ c.label = some (.Q, u)

/-- The graph on the atoms whose edges are the waved edges. -/
def Graph.wavedGraph {k n : ℕ} (Γ : Graph k n) : SimpleGraph (Atom k n) :=
  SimpleGraph.fromRel fun u v => ∃ c ∈ Γ.comps, (∃ w, c.kind = .waved w) ∧ c.x = u ∧ c.y = v

/-- The graph on the atoms whose edges are all components except the `×`-dotted edges. -/
def Graph.edgeGraphNoX {k n : ℕ} (Γ : Graph k n) : SimpleGraph (Atom k n) :=
  SimpleGraph.fromRel fun u v => ∃ c ∈ Γ.comps, c.kind ≠ .xdot ∧ c.x = u ∧ c.y = v

/-- The graph stays connected when its `×`-dotted edges are removed. -/
def Graph.ConnNoX {k n : ℕ} (Γ : Graph k n) : Prop := Γ.edgeGraphNoX.Preconnected

/-! ## The model relations -/

/-- The relations of the random band matrix model on which the value identities of
[I, §2.1, §3] = [II, §4] rest, for a data record `D` and conditional expectations `PF` on a
sample space `Ω`
([I, Assumption 1.1, (1.1), (1.16), (1.39), (2.1), §1.4]; [II, (4.17), (4.20)]):

* a Hermitian matrix field `H`, a spectral parameter `z` with `Im z > 0`, a real symmetric
  `S ≥ 0` with row sums `1`;
* the data record: `m = m_sc(z)`; `G = (H - z)⁻¹`; the minor entries
  `G^{(x)}_{ab} = G_{ab} - G_{ax} G_{xb} / G_{xx}`; `s_{xy}`; `(1 - m² S)(1 + S⁺) = 1`;
  `S⁻ = \overline{S⁺}`; `Θ (1 - |m|² S) = |m|² S`;
* the laws of the partial expectations `P_x` on a class `Good` (with `Meas x`: independent of
  the `x`-th row and column of `H`, closed under sums and products, satisfied by `G^{(x)}`
  entries); `P_x \overline{F} = \overline{P_x F}`; `Good` contains the entries of `H`, the
  resolvent entries, their minors and `(G_{xx})⁻¹`, and is closed under conjugation;
* a class `Test ⊆ Good` of test functions closed under sums, products, conjugation and the
  derivatives `∂_{h_{ab}}` (`dh a b`), which are additive, satisfy the product rule, vanish on
  constants and act on resolvent entries by [I, (3.8)];
* Gaussian integration by parts inside `P_x`: `P_x[h_{ab} F] = s_{ab} P_x[∂_{h_{ba}} F]` for
  every entry `h_{ab}` of the `x`-th row or column ([I, Lemma 2.4]).

The fields `Sig`, `ThetaErr`, `ghost`, `aux` of `D` are not constrained. -/
structure ModelAdm (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι)
    (D : Ω → Data ι) where
  H : Ω → Matrix ι ι ℂ
  z : ℂ
  S : Matrix ι ι ℝ
  E : (Ω → ℂ) → ℂ
  Meas : ι → (Ω → ℂ) → Prop
  Good : (Ω → ℂ) → Prop
  Test : (Ω → ℂ) → Prop
  dh : ι → ι → (Ω → ℂ) → Ω → ℂ
  isHermitian : ∀ ω, (H ω).IsHermitian
  im_pos : 0 < z.im
  isSymm : S.IsSymm
  nonneg : ∀ x y, 0 ≤ S x y
  rowSum : ∀ x, ∑ y, S x y = 1
  data_m : ∀ ω, (D ω).m = msc z
  data_G : ∀ ω, (D ω).Gm ∅ = green (H ω) z
  data_minor : ∀ ω x, (D ω).Gm {x} = Matrix.of (greenMinor (green (H ω) z) x)
  data_S : ∀ ω, (D ω).S = S.map fun r => (r : ℂ)
  data_Sp : ∀ ω, (1 - msc z ^ 2 • (D ω).S) * (1 + (D ω).Sp) = 1
  data_Sm : ∀ ω, (D ω).Sm = (D ω).Sp.map star
  data_Theta : ∀ ω, (D ω).Theta * (1 - ((‖msc z‖ ^ 2 : ℝ) : ℂ) • (D ω).S) =
    ((‖msc z‖ ^ 2 : ℝ) : ℂ) • (D ω).S
  laws : PF.Laws E Meas Good
  meas_add : ∀ x F G, Meas x F → Meas x G → Meas x (F + G)
  meas_mul : ∀ x F G, Meas x F → Meas x G → Meas x (F * G)
  meas_minor : ∀ x a b, Meas x fun ω => (D ω).Gm {x} a b
  P_star : ∀ x F, Good F → PF.P x (fun ω => star (F ω)) = fun ω => star (PF.P x F ω)
  good_star : ∀ F, Good F → Good fun ω => star (F ω)
  good_entry : ∀ T a b, Good fun ω => (D ω).Gm T a b
  good_inv : ∀ a, Good fun ω => ((D ω).Gm ∅ a a)⁻¹
  good_H : ∀ a b, Good fun ω => H ω a b
  test_good : ∀ F, Test F → Good F
  test_const : ∀ c : ℂ, Test fun _ => c
  test_add : ∀ F G, Test F → Test G → Test (F + G)
  test_mul : ∀ F G, Test F → Test G → Test (F * G)
  test_star : ∀ F, Test F → Test fun ω => star (F ω)
  test_entry : ∀ a b, Test fun ω => (D ω).Gm ∅ a b
  test_dh : ∀ a b F, Test F → Test (dh a b F)
  dh_add : ∀ a b F G, Test F → Test G → dh a b (F + G) = dh a b F + dh a b G
  dh_mul : ∀ a b F G, Test F → Test G → dh a b (F * G) = dh a b F * G + F * dh a b G
  dh_const : ∀ a b (c : ℂ), dh a b (fun _ => c) = 0
  dh_green : ∀ a b x y,
    dh a b (fun ω => green (H ω) z x y) = fun ω => -(green (H ω) z x a * green (H ω) z b y)
  dh_conj_green : ∀ a b x y, dh a b (fun ω => star (green (H ω) z x y)) =
    fun ω => -(star (green (H ω) z x b) * star (green (H ω) z a y))
  ibp : ∀ x a b, (a = x ∨ b = x) → ∀ F, Test F →
    PF.P x (fun ω => H ω a b * F ω) = fun ω => (S a b : ℂ) * PF.P x (dh b a F) ω

/-- The admissibility predicate of the value identities: the model relations hold. -/
def modelAdm : ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι], PFamily Ω ι → (Ω → Data ι) → Prop :=
  fun Ω ι _ _ PF D => Nonempty (ModelAdm Ω ι PF D)

/-- The resolvent entry `G_{ab}` at `ω`. -/
def ModelAdm.G {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
    (A : ModelAdm Ω ι PF D) (ω : Ω) (a b : ι) : ℂ :=
  green (A.H ω) A.z a b

/-- The data record of the model at the sample `ω`: `m = m_sc(z)`, `G = (H - z)⁻¹` and its
minors `G^{(x)}`, `s`, `S^± = m², m̄² S (1 - m², m̄² S)⁻¹`, `Θ = |m|² S (1 - |m|² S)⁻¹`; the
other fields are `0`. -/
def modelData {Ω ι : Type} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (z : ℂ)
    (H : Ω → Matrix ι ι ℂ) (ω : Ω) : Data ι where
  m := msc z
  Gm T := if h : ∃ x, T = {x} then Matrix.of (greenMinor (green (H ω) z) h.choose)
    else green (H ω) z
  S := S.map fun r => (r : ℂ)
  Sp := (msc z ^ 2 • S.map fun r => (r : ℂ)) * (1 - msc z ^ 2 • S.map fun r => (r : ℂ))⁻¹
  Sm := ((msc z ^ 2 • S.map fun r => (r : ℂ)) *
    (1 - msc z ^ 2 • S.map fun r => (r : ℂ))⁻¹).map star
  Theta := (((‖msc z‖ ^ 2 : ℝ) : ℂ) • S.map fun r => (r : ℂ)) *
    (1 - ((‖msc z‖ ^ 2 : ℝ) : ℂ) • S.map fun r => (r : ℂ))⁻¹
  Sig _ := 0
  ThetaErr _ _ := 0
  ghost := 0
  aux _ := 0

/-- The model relations hold for the Gaussian model: with `Ω`, `hmat`, `Pexp` the sample space,
the matrix `H(ω)` and the partial expectations `P_x` of [I, Assumption 1.1, §1.4], every real
symmetric `S ≥ 0` with row sums `1` and every `z` with `Im z > 0` give model relations for
`modelData`. -/
def modelAdm_gaussStmt (ι Ω : Type) [Fintype ι] [DecidableEq ι] (hmat : Ω → Matrix ι ι ℂ)
    (Pexp : Matrix ι ι ℝ → ι → (Ω → ℂ) → Ω → ℂ) : Prop :=
  ∀ (S : Matrix ι ι ℝ) (z : ℂ), S.IsSymm → (∀ x y, 0 ≤ S x y) → (∀ x, ∑ y, S x y = 1) →
    0 < z.im → Nonempty (ModelAdm Ω ι ⟨Pexp S⟩ (modelData S z hmat))

/-- The graph `T_{a,b₁b₂} = |m|² ∑_x s_{ax} G_{xb₁} Ḡ_{xb₂}` of [I, (2.4)]; external atoms
`a = 0`, `b₁ = 1`, `b₂ = 2`, internal atom `x`. -/
def tGraph : Graph 3 1 :=
  ⟨[mkC (.waved .s) (.inl 0) (.inr 0), mkC (.G .plus) (.inr 0) (.inl 1),
    mkC (.G .minus) (.inr 0) (.inl 2)], cm * cmb⟩

/-- The right side of [I, (2.7)]: `m Θ_{ab₁} Ḡ_{b₁b₂}`, the two graphs of `A^{(>2)}` of
[I, (2.8)] and the four graphs of `Q^{(2)}` of [I, (2.9)]; internal atoms `x = 0`, `y = 1`. -/
def secondOrderExp : Expansion 3 :=
  let a : Atom 3 2 := .inl 0
  let b₁ : Atom 3 2 := .inl 1
  let b₂ : Atom 3 2 := .inl 2
  let x : Atom 3 2 := .inr 0
  let y : Atom 3 2 := .inr 1
  let x₁ : Atom 3 1 := .inr 0
  [⟨0, ⟨[mkC (.theta []) (.inl 0) (.inl 1), mkC (.G .minus) (.inl 1) (.inl 2)], cm⟩⟩,
    ⟨2, ⟨[mkC (.theta []) a x, mkC (.waved .s) x y, mkC (.light .plus) y y,
      mkC (.G .plus) x b₁, mkC (.G .minus) x b₂], cm⟩⟩,
    ⟨2, ⟨[mkC (.theta []) a x, mkC (.waved .s) x y, mkC (.light .minus) x x,
      mkC (.G .plus) y b₁, mkC (.G .minus) y b₂], cm⟩⟩,
    ⟨1, ⟨[mkC (.theta []) (.inl 0) x₁] ++
      labelQs x₁ [mkC (.G .plus) x₁ (.inl 1), mkC (.G .minus) x₁ (.inl 2)], 1⟩⟩,
    ⟨0, ⟨[mkC (.theta []) (.inl 0) (.inl 1)] ++
      labelQs (.inl 1) [mkC (.G .minus) (.inl 1) (.inl 2)],
      -cm⟩⟩,
    ⟨2, ⟨[mkC (.theta []) a x, mkC (.waved .s) x y] ++
      labelQs x [mkC (.light .plus) y y, mkC (.G .plus) x b₁, mkC (.G .minus) x b₂], -cm⟩⟩,
    ⟨2, ⟨[mkC (.theta []) a x, mkC (.waved .s) x y] ++
      labelQs x [mkC (.weight .minus) x x, mkC (.G .plus) y b₁, mkC (.G .minus) y b₂], -cm⟩⟩]

/-- The canonical properties (ii)–(iv) of [I, Def 3.8] for a tracked operator at an internal
atom: on a plain normal regular graph with bound `C`, every output graph is plain and normal
regular with bound `C' C`, has scaling order at least that of the input, and every new atom is
joined to the image of `x` by a path of waved edges. -/
def CanonicalAt (O : ∀ {k n : ℕ}, Atom k n → Graph k n → TExpansion k n) (C' : ℕ → ℕ) : Prop :=
  ∀ (k n C : ℕ) (x : Atom k n) (Γ : Graph k n), x.isRight = true → Γ.Normal C → Γ.Plain →
    ∀ t ∈ O x Γ, t.g.Normal (C' C) ∧ t.g.Plain ∧ Γ.ord ≤ t.g.ord ∧
      ∀ u, t.IsNew u → t.g.wavedGraph.Reachable (t.f x) u

/-- The degree pattern of case (b) of [I, Lemmas 3.16, 3.19]: the two solid edges between `x` and
`y` are removed (`deg x` becomes `0`, `deg y` drops by `2`), the other degrees are unchanged and
the new atoms have degree `0`. -/
def Tracked.PairRemoved {k n : ℕ} (t : Tracked k n) (Γ : Graph k n) (x y : Atom k n) : Prop :=
  t.g.ord = Γ.ord ∧ t.g.deg (t.f x) = 0 ∧ t.g.deg (t.f y) + 2 = Γ.deg y ∧
    (∀ v, v ≠ x → v ≠ y → t.g.deg (t.f v) = Γ.deg v) ∧ ∀ u, t.IsNew u → t.g.deg u = 0

/-- The coefficient `m⁻¹` (charge `plus`) or `m̄⁻¹` (charge `minus`). -/
def mInvOf : Charge → Coeff
  | .plus => MvPolynomial.X .mInv
  | .minus => MvPolynomial.X .mBarInv

/-- The graph without its `P`/`Q` labels. -/
def Graph.dropLabels {k n : ℕ} (Γ : Graph k n) : Graph k n :=
  ⟨Γ.comps.map fun c => { c with label := none }, Γ.coeff⟩

section Instances

open Complex

end Instances

end RBM8D.Graphs
