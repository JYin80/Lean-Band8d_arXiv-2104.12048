import RBM8D.Graph.QExp.Steps
import RBM8D.Graph.Local.Edge

/-!
# Blocks, elementary steps and the statements of the `Q`-expansions

Blocks of atoms joined by dotted edges and the dot excess; the elementary steps of the
construction of [II, §4.4] (`QElemStep`); the clauses on the output graphs; the statements of
[II, Lemmas 4.11, 4.13, 4.14, 4.15] as propositions.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## Blocks and the dot excess -/

/-- The graph on the atoms whose edges are the dotted edges. -/
def Graph.dotGraph {k n : ℕ} (Γ : Graph k n) : SimpleGraph (Atom k n) :=
  SimpleGraph.fromRel fun u v => ∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = u ∧ c.y = v

/-- `u` and `v` lie in one block: they are equal or joined by a path of dotted edges (in the
value, `σ u = σ v` on every nonzero term). -/
def Graph.SameBlock {k n : ℕ} (Γ : Graph k n) (u v : Atom k n) : Prop :=
  Γ.dotGraph.Reachable u v

/-- The number of dotted edges, loops included. -/
def Graph.nDots {k n : ℕ} (Γ : Graph k n) : ℕ :=
  (Γ.comps.filter fun c => decide (c.kind = .dot)).length

/-- The dot excess: the number of dotted edges minus the number of edges of a spanning forest
of the blocks, `#dots - (k + n - #blocks)`. It is `0` exactly when the dotted edges form a
forest without loops. -/
def Graph.dotExcess {k n : ℕ} (Γ : Graph k n) : ℤ :=
  (Γ.nDots : ℤ) - ((k + n : ℕ) : ℤ) + (Nat.card Γ.dotGraph.ConnectedComponent : ℤ)

/-- No `×`-dotted edge joins two atoms of one block; in particular there is no `×`-dotted loop.
The graphs excluded have value `0` ([I, Def 2.6]). -/
def Graph.XdotApart {k n : ℕ} (Γ : Graph k n) : Prop :=
  ∀ c ∈ Γ.comps, c.kind = .xdot → ¬ Γ.SameBlock c.x c.y

/-- No `G^{(T)}` entry, no `(G_{xx})⁻¹` weight, no dotted loop `1_{u = u}`, and every component
well formed; `W_D` weights are allowed. These are the graphs of scaling order `> D` of
[II, Lemmas 4.11, 4.13–4.15]. -/
def Graph.Clean {k n : ℕ} (Γ : Graph k n) : Prop :=
  ∀ c ∈ Γ.comps, c.minor = [] ∧ (∀ ch, c.kind ≠ .inv ch) ∧ (c.kind = .dot → c.x ≠ c.y) ∧ c.WF

/-- No weight and no solid edge without label is attached to an atom of the block of `u`
(`Γ₀` has no weights or edges attached to `x`, [II, Lemmas 4.11, 4.15 (iv)]). -/
def Graph.UnlabelledFreeAtBlock {k n : ℕ} (Γ : Graph k n) (u : Atom k n) : Prop :=
  ∀ c ∈ Γ.comps, c.label = none → c.kind.isRandom = true →
    ¬ Γ.SameBlock c.x u ∧ ¬ Γ.SameBlock c.y u

/-- No labelled weight and no labelled solid edge is attached to an atom of the block of `u`
(`𝒢` has no weights or edges attached to `x` in `P_x(𝒢)`, [II, Lemmas 4.13, 4.14]). -/
def Graph.LabelledFreeAtBlock {k n : ℕ} (Γ : Graph k n) (u : Atom k n) : Prop :=
  ∀ c ∈ Γ.comps, c.label.isSome = true → c.kind.isRandom = true →
    ¬ Γ.SameBlock c.x u ∧ ¬ Γ.SameBlock c.y u

/-- Graphs `Γ P_u(𝒢)`: every label is `P_u` and some component carries it; the unlabelled
components form `Γ`, the labelled ones `𝒢`. -/
def Graph.IsPFormAt {k n : ℕ} (Γ : Graph k n) (u : Atom k n) : Prop :=
  (∃ c ∈ Γ.comps, c.label = some (.P, u)) ∧ ∀ c ∈ Γ.comps, c.label = none ∨ c.label = some (.P, u)

/-- `u` has been identified with `v` (they lie in one block) or is joined to `v` by a solid edge
without label ([II, Lemma 4.11], [II, Lemma 4.15 (iv)]). -/
def Graph.QJoined {k n : ℕ} (Γ : Graph k n) (u v : Atom k n) : Prop :=
  Γ.SameBlock u v ∨ ∃ c ∈ Γ.comps, c.kind.isSolid = true ∧ c.label = none ∧
    (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)

/-! ## Elementary steps of the construction -/

/-- The resolvent identity [II, (4.17)] at the weight or light weight with index `i` on an atom
`a ≠ x`: `G_{aa} = G^{(x)}_{aa} + G_{ax} G_{xa} (G_{xx})⁻¹` and
`G_{aa} - m = (G^{(x)}_{aa} - m) + G_{ax} G_{xa} (G_{xx})⁻¹` (their complex conjugates for the
charge `minus`), the label of the weight kept on the new factors; the identity if that component
is not such a weight without minor, or if its label is also carried by a component not of a kind
of `Comp.isGoodKind`. -/
def oSchurWT {k n : ℕ} (x : Atom k n) (i : ℕ) (Γ : Graph k n) : TExpansion k n :=
  match Γ.comps[i]? with
  | some c =>
    match c.kind with
    | .weight ch | .light ch =>
      if c.minor.isEmpty && c.x != x && c.label.all Γ.GoodGroup then
        let rest := Γ.comps.eraseIdx i
        [⟨n, ⟨rest ++ [{ c with minor := [x] }], Γ.coeff⟩, id⟩,
          ⟨n, ⟨rest ++ [{ mkC (.G ch) c.x x with label := c.label },
            { mkC (.G ch) x c.x with label := c.label },
            { mkC (.inv ch) x x with label := c.label }], Γ.coeff⟩, id⟩]
      else [Tracked.self Γ]
    | _ => [Tracked.self Γ]
  | none => [Tracked.self Γ]

/-- The resolvent identity [II, (4.20)] at the weight or light weight with index `i` and minor
`{x}` on an atom `a ≠ x`: `G^{(x)}_{aa} = G_{aa} - G_{ax} G_{xa} (G_{xx})⁻¹` (and the same for
`G^{(x)}_{aa} - m`, and the complex conjugates), the label kept on the new factors; the identity
if that component is not such a weight, or if its label is also carried by a component not of a
kind of `Comp.isGoodKind`. -/
def oSchurWRevT {k n : ℕ} (x : Atom k n) (i : ℕ) (Γ : Graph k n) : TExpansion k n :=
  match Γ.comps[i]? with
  | some c =>
    match c.kind with
    | .weight ch | .light ch =>
      if c.minor = [x] && c.x != x && c.label.all Γ.GoodGroup then
        let rest := Γ.comps.eraseIdx i
        [⟨n, ⟨rest ++ [{ c with minor := [] }], Γ.coeff⟩, id⟩,
          ⟨n, ⟨rest ++ [{ mkC (.G ch) c.x x with label := c.label },
            { mkC (.G ch) x c.x with label := c.label },
            { mkC (.inv ch) x x with label := c.label }], -Γ.coeff⟩, id⟩]
      else [Tracked.self Γ]
    | _ => [Tracked.self Γ]
  | none => [Tracked.self Γ]

/-- The partition `1 = 1_{u = v} + 1_{u ≠ v}`: `Γ` with a dotted edge between `u` and `v`, and
`Γ` with a `×`-dotted edge between `u` and `v`; the identity if `u = v`. -/
def oSplitT {k n : ℕ} (u v : Atom k n) (Γ : Graph k n) : TExpansion k n :=
  if u = v then [Tracked.self Γ] else
    [Tracked.self ⟨Γ.comps ++ [mkC .dot u v], Γ.coeff⟩,
      Tracked.self ⟨Γ.comps ++ [mkC .xdot u v], Γ.coeff⟩]

/-- The identity `1_{u ≠ v} = 1 - 1_{u = v}` at the `×`-dotted edge with index `i` when no solid
edge joins its ends: `Γ` without that edge, and `-Γ` with a dotted edge in its place; the
identity otherwise. -/
def oXdotT {k n : ℕ} (i : ℕ) (Γ : Graph k n) : TExpansion k n :=
  match Γ.comps[i]? with
  | some c =>
    if c.kind = .xdot ∧ c.label = none ∧ (Γ.comps.any fun d => d.kind.isSolid &&
        ((d.x == c.x && d.y == c.y) || (d.x == c.y && d.y == c.x))) = false then
      [Tracked.self ⟨Γ.comps.eraseIdx i, Γ.coeff⟩,
        Tracked.self ⟨Γ.comps.eraseIdx i ++ [mkC .dot c.x c.y], -Γ.coeff⟩]
    else [Tracked.self Γ]
  | none => [Tracked.self Γ]

/-- The identity `Q_u = 1 - P_u` on the label group `Q_u`: `Γ` without labels, and `-Γ` with every
label `Q_u` replaced by `P_u`. -/
def oQPT {k n : ℕ} (u : Atom k n) (Γ : Graph k n) : TExpansion k n :=
  [Tracked.self Γ.dropLabels,
    Tracked.self ⟨Γ.comps.map fun c =>
      if c.label = some (.Q, u) then { c with label := some (.P, u) } else c, -Γ.coeff⟩]

/-- The random components without label whose minor contains the atom of `ℓ` moved into the
label group `ℓ` (a factor independent of the row of that atom commutes with `P_u` and `Q_u`). -/
def Graph.absorb {k n : ℕ} (ℓ : PQ × Atom k n) (Γ : Graph k n) : Graph k n :=
  ⟨Γ.comps.map fun c =>
    if c.label = none ∧ c.kind.isRandom = true ∧ ℓ.2 ∈ c.minor then { c with label := some ℓ }
    else c, Γ.coeff⟩

/-- The labelled components of `Γ` without their labels, together with the components that are
not random: in `Γ_ω P_u(𝒢)`, the graph `𝒢` with the deterministic part of `Γ_ω` (dotted,
`×`-dotted, waved and `Θ` edges), on which the identities [II, (4.23), (4.24)] act. -/
def Graph.pCore {k n : ℕ} (Γ : Graph k n) : Graph k n :=
  ⟨(Γ.comps.filter fun c => c.label.isSome || !c.kind.isRandom).map fun c =>
    { c with label := none }, Γ.coeff⟩

/-- The random components without label of `Γ`: the random factors of `Γ_ω` in `Γ_ω P_u(𝒢)`. -/
def Graph.pEnv {k n : ℕ} (Γ : Graph k n) : List (Comp (Atom k n)) :=
  Γ.comps.filter fun c => c.label.isNone && c.kind.isRandom

/-- A tracked formal sum `E` of graphs obtained from `Γ.pCore`, read inside `P_u`: in every term the
random components get the label `P` at the image of `u` and the random factors of `Γ_ω` are put
back at the images of their atoms; the terms with a label `Q` at the image of `u` are dropped
(`P_u Q_u = 0`). -/
def pLiftT {k n : ℕ} (u : Atom k n) (Γ : Graph k n) (E : TExpansion k n) : TExpansion k n :=
  E.filterMap fun t =>
    if t.g.comps.any (fun c => decide (c.label = some (.Q, t.f u))) then none
    else some ⟨t.nOut, ⟨t.g.comps.map (fun c =>
        if c.kind.isRandom then { c with label := some (.P, t.f u) } else c) ++
      Γ.pEnv.map (Comp.map t.f), t.g.coeff⟩, t.f⟩

/-- The identity [II, (4.23)] for `P_x[(G_{xx} - m) f(G)]` at the first light weight of positive
charge on `x` of `Γ` (`none` if there is none). The new atom is `α`; the terms are, in order:
`m² ∑_α s_{xα} (G_{αα} - m) f`, `m ∑_α s_{xα} (G_{αα} - m)(G_{xx} - m) f`, and
`-m ∑_α s_{xα} G_{αx} ∂_{h_{αx}} f`. -/
def oWeightP2Pos {k n : ℕ} (x : Atom k n) (Γ : Graph k n) : Option (TExpansion k n) :=
  match Γ.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) with
  | none => none
  | some i =>
    let x₁ : Atom k (n + 1) := liftA 1 x
    let a₁ : Atom k (n + 1) := newA 0
    let F₁ := liftCs 1 (Γ.comps.eraseIdx i)
    let sx : Comp (Atom k (n + 1)) := mkC (.waved .s) x₁ a₁
    let t₁ (cs : List (Comp (Atom k (n + 1)))) (d : Coeff) : Tracked k n :=
      ⟨n + 1, ⟨cs, d⟩, liftA 1⟩
    some <|
      [t₁ (F₁ ++ [sx, mkC (.light .plus) a₁ a₁]) (cm * cm * Γ.coeff),
        t₁ (liftCs 1 Γ.comps ++ [sx, mkC (.light .plus) a₁ a₁]) (cm * Γ.coeff)] ++
      (dTerms a₁ x₁ F₁).map fun d => t₁ (d ++ [sx, mkC (.G .plus) a₁ x₁]) (cm * Γ.coeff)

/-- The operator `Õ^{(x),2}_weight` of [II, §4.4, Step 2] on `Γ_ω P_x(𝒢)`: [II, (4.23)] applied
to `𝒢` inside `P_x` at its first light weight of positive charge on `x`, otherwise (complex
conjugation) at its first light weight of negative charge on `x`; the identity if `𝒢` has no
light weight on `x`. -/
def oWeightP2T {k n : ℕ} (x : Atom k n) (Γ : Graph k n) : TExpansion k n :=
  match oWeightP2Pos x Γ.pCore with
  | some E => pLiftT x Γ E
  | none =>
    match oWeightP2Pos x Γ.pCore.conj with
    | some E => pLiftT x Γ E.conj
    | none => [Tracked.self Γ]

/-- One elementary step of the construction of the `Q`-expansions ([II, §4.4]): the second graph
is a term of one of the following operations applied to the first.
* `schur`, `schurRev`, `schurW`, `schurWRev`: [II, (4.17), (4.20)] at a solid edge, or at a weight
  or light weight, at an internal atom `x`.
* `taylor`: [II, (4.21)].
* `weight1`: `O^{(x),1}_weight` on the weights without label.
* `dot`, `merge`: `O_dot` and `O_merge` ([II, Defs 4.1, 4.2]).
* `split`: `1 = 1_{u = v} + 1_{u ≠ v}` with `v` internal.
* `xdot`: `1_{u ≠ v} = 1 - 1_{u = v}` at a `×`-dotted edge without solid edge.
* `dropDot`: removal of a dotted edge whose ends are joined by the other dotted edges (a dotted
  loop included).
* `rebase`: an end of a component other than a dotted edge moved to an atom of its block.
* `qToP`: `Q_u = 1 - P_u` on a graph `Γ Q_u(𝒢)`.
* `absorb`: factors with minor `{u}` moved into the label group.
* `dropP`: the label `P_u` removed from a group of factors all with `u` in their minor.
* `pWeight1`, `pWeight2`, `pMultiE`: `O^{(x),1}_weight`, [II, (4.23)] and [II, (4.24)] inside
  `P_x` on a normal regular graph `Γ_ω P_x(𝒢)`. -/
inductive QElemStep {k : ℕ} : (Σ n, Graph k n) → (Σ n, Graph k n) → Prop
  | schur {n : ℕ} (x : Atom k n) (i : ℕ) (Γ : Graph k n) (t : Tracked k n)
      (hx : x.isRight = true) (ht : t ∈ oSchurT x i Γ) : QElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩
  | schurRev {n : ℕ} (x : Atom k n) (i : ℕ) (Γ : Graph k n) (t : Tracked k n)
      (hx : x.isRight = true) (ht : t ∈ oSchurRevT x i Γ) : QElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩
  | schurW {n : ℕ} (x : Atom k n) (i : ℕ) (Γ : Graph k n) (t : Tracked k n)
      (hx : x.isRight = true) (ht : t ∈ oSchurWT x i Γ) : QElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩
  | schurWRev {n : ℕ} (x : Atom k n) (i : ℕ) (Γ : Graph k n) (t : Tracked k n)
      (hx : x.isRight = true) (ht : t ∈ oSchurWRevT x i Γ) : QElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩
  | taylor {n : ℕ} (D i : ℕ) (Γ : Graph k n) (t : Tracked k n) (ht : t ∈ oTaylorT D i Γ) :
      QElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩
  | weight1 {n : ℕ} (x : Atom k n) (Γ : Graph k n) (t : Tracked k n)
      (ht : t ∈ oWeight1T x Γ) : QElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩
  | dot {n : ℕ} (Γ : Graph k n) (t : Tracked k n) (ht : t ∈ oDotT Γ) :
      QElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩
  | merge {n : ℕ} (Γ : Graph k n) (t : Tracked k n) (ht : Γ.mergeT = some t) :
      QElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩
  | split {n : ℕ} (u v : Atom k n) (Γ : Graph k n) (t : Tracked k n) (hv : v.isRight = true)
      (ht : t ∈ oSplitT u v Γ) : QElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩
  | xdot {n : ℕ} (i : ℕ) (Γ : Graph k n) (t : Tracked k n) (ht : t ∈ oXdotT i Γ) :
      QElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩
  | dropDot {n : ℕ} (i : ℕ) (Γ : Graph k n) (c : Comp (Atom k n)) (hc : Γ.comps[i]? = some c)
      (hk : c.kind = .dot)
      (hb : (⟨Γ.comps.eraseIdx i, Γ.coeff⟩ : Graph k n).SameBlock c.x c.y) :
      QElemStep ⟨n, Γ⟩ ⟨n, ⟨Γ.comps.eraseIdx i, Γ.coeff⟩⟩
  | rebase {n : ℕ} (i : ℕ) (Γ : Graph k n) (c : Comp (Atom k n)) (u v : Atom k n)
      (hc : Γ.comps[i]? = some c) (hk : c.kind ≠ .dot) (hb : Γ.SameBlock u v) :
      QElemStep ⟨n, Γ⟩ ⟨n, ⟨Γ.comps.set i
        { c with x := if c.x = u then v else c.x, y := if c.y = u then v else c.y }, Γ.coeff⟩⟩
  | qToP {n : ℕ} (u : Atom k n) (Γ : Graph k n) (t : Tracked k n) (hQ : Γ.IsQFormAt u)
      (ht : t ∈ oQPT u Γ) : QElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩
  | absorb {n : ℕ} (ℓ : PQ × Atom k n) (Γ : Graph k n) (hℓ : ∃ c ∈ Γ.comps, c.label = some ℓ)
      (hl : ∀ c ∈ Γ.comps, c.label = none ∨ c.label = some ℓ) :
      QElemStep ⟨n, Γ⟩ ⟨n, Γ.absorb ℓ⟩
  | dropP {n : ℕ} (u : Atom k n) (Γ : Graph k n) (hP : Γ.IsPFormAt u)
      (hm : ∀ c ∈ Γ.comps, c.label.isSome = true → u ∈ c.minor) :
      QElemStep ⟨n, Γ⟩ ⟨n, Γ.dropLabels⟩
  | pWeight1 {n : ℕ} (x : Atom k n) (Γ : Graph k n) (t : Tracked k n) (hP : Γ.IsPFormAt x)
      (hp : Γ.Plain) (ht : t ∈ pLiftT x Γ (oWeight1T x Γ.pCore)) :
      QElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩
  | pWeight2 {n : ℕ} (x : Atom k n) (Γ : Graph k n) (t : Tracked k n) (hP : Γ.IsPFormAt x)
      (hp : Γ.Plain) (ht : t ∈ oWeightP2T x Γ) : QElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩
  | pMultiE {n : ℕ} (x : Atom k n) (Γ : Graph k n) (E : TExpansion k n) (t : Tracked k n)
      (hP : Γ.IsPFormAt x) (hp : Γ.Plain) (hE : multiEHat x Γ.pCore = some E)
      (ht : t ∈ pLiftT x Γ E) : QElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩

/-! ## Clauses on the output graphs -/

/-- The clauses on every output graph `t` of an expansion of `Γ` at `x`: normal regular with
bound `C'`; scaling order at least that of `Γ`; no `×`-dotted edge inside a block; dot excess at
most that of `Γ`; the image of `x` is internal; the doubly connected property is kept
([II, Lemma 4.15 (i), (iii)]); `t` is reached from `Γ` by a chain of elementary steps
`QElemStep`. -/
def Tracked.QBase {k n : ℕ} (C' : ℕ) (x : Atom k n) (Γ : Graph k n) (t : Tracked k n) : Prop :=
  t.g.Normal C' ∧ Γ.ord ≤ t.g.ord ∧ t.g.XdotApart ∧ t.g.dotExcess ≤ Γ.dotExcess ∧
    (t.f x).isRight = true ∧ (Γ.DoublyConnected → t.g.DoublyConnected) ∧
    Relation.ReflTransGen QElemStep ⟨n, Γ⟩ ⟨t.nOut, t.g⟩

/-- Some weight or solid edge without label of `Γ` has an atom whose image is identified with the
image of `x` or joined to it by a solid edge without label ([II, Lemma 4.11],
[II, Lemma 4.15 (iv)]). -/
def Tracked.QWitness {k n : ℕ} (x : Atom k n) (Γ : Graph k n) (t : Tracked k n) : Prop :=
  ∃ c ∈ Γ.comps, c.label = none ∧ c.kind.isRandom = true ∧
    ∃ u ∈ [c.x, c.y], t.g.QJoined (t.f u) (t.f x)

/-- The unlabelled components of `Γ` other than dotted and `×`-dotted edges are kept, at the
images of their atoms, and blocks are mapped into blocks (the factor `Γ_ω` of `Γ_ω P_x(𝒢)` in
[II, §4.4, Steps 2, 3]). -/
def Tracked.Carries {k n : ℕ} (Γ : Graph k n) (t : Tracked k n) : Prop :=
  ((Γ.comps.filter fun c => decide (c.label = none ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)).map
      (Comp.map t.f)).Subperm t.g.comps ∧
    ∀ u v, Γ.SameBlock u v → t.g.SameBlock (t.f u) (t.f v)

/-- The clauses of [II, Lemma 4.11] on an output graph `t`: the clauses `Tracked.QBase`; no new
atom; `t` is of the form `Γ_ω Q_x(Γ̃_ω)` or `Q_x(𝒢_ζ)` without `G^{(T)}`, `(G_{xx})⁻¹`, `W_D`
components, or of scaling order `> D`; if `Γ₀` has no weights or edges attached to the block of
`x`, a graph `Γ_ω Q_x(Γ̃_ω)` that is not a `Q`-graph has a strictly higher scaling order and an
atom of a weight or edge of `Γ₀` identified with `x` or joined to `x` by a solid edge. -/
def qStep1Out {k n : ℕ} (D C' : ℕ) (x : Atom k n) (Γ : Graph k n) (t : Tracked k n) : Prop :=
  t.QBase C' x Γ ∧ (∀ u, ¬ t.IsNew u) ∧
    ((t.g.Plain ∧ t.g.IsQFormAt (t.f x)) ∨ ((D : ℤ) + 1 ≤ t.g.ord ∧ t.g.Clean)) ∧
    (Γ.UnlabelledFreeAtBlock x → t.g.Plain → t.g.IsQFormAt (t.f x) → ¬ t.g.IsQGraphAt (t.f x) →
      Γ.ord + 1 ≤ t.g.ord ∧ t.QWitness x Γ)

/-- The clauses of [II, Lemma 4.15] on an output graph `t`: the clauses `Tracked.QBase` ((i),
(iii)); `t` is without labels or a `Q`-graph with the label `Q_x`, without `G^{(T)}`,
`(G_{xx})⁻¹`, `W_D` components, or of scaling order `> D`; (ii) new atoms are joined to `x` by
waved edges; (iv) if `Γ₀` has no weights or edges attached to the block of `x`, every output
graph without labels and of scaling order `≤ D` has a strictly higher scaling order and an atom
of a weight or edge of `Γ₀` identified with `x` or joined to `x` by a solid edge. -/
def qExpansionOut {k n : ℕ} (D C' : ℕ) (x : Atom k n) (Γ : Graph k n) (t : Tracked k n) :
    Prop :=
  t.QBase C' x Γ ∧
    ((t.g.Plain ∧ (t.g.LabelFree ∨ t.g.IsQGraphAt (t.f x))) ∨
      ((D : ℤ) + 1 ≤ t.g.ord ∧ t.g.Clean)) ∧
    (∀ u, t.IsNew u → t.g.wavedGraph.Reachable (t.f x) u) ∧
    (Γ.UnlabelledFreeAtBlock x → t.g.LabelFree → t.g.ord ≤ D →
      Γ.ord + 1 ≤ t.g.ord ∧ t.QWitness x Γ)

/-! ## Facts on blocks and the dot excess -/

/-- If every dotted edge is a loop, the graph of dotted edges has no edge. -/
theorem Graph.dotGraph_eq_bot {k n : ℕ} (Γ : Graph k n)
    (h : ∀ c ∈ Γ.comps, c.kind = .dot → c.x = c.y) : Γ.dotGraph = ⊥ := by
  ext u v
  simp only [Graph.dotGraph, SimpleGraph.fromRel_adj, SimpleGraph.bot_adj, iff_false, not_and]
  rintro huv (⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩)
  · exact huv (h c hc hk)
  · exact huv (h c hc hk).symm

/-- If every dotted edge is a loop, two atoms lie in one block exactly when they are equal. -/
theorem Graph.sameBlock_iff_eq {k n : ℕ} (Γ : Graph k n)
    (h : ∀ c ∈ Γ.comps, c.kind = .dot → c.x = c.y) (u v : Atom k n) :
    Γ.SameBlock u v ↔ u = v := by
  rw [Graph.SameBlock, Graph.dotGraph_eq_bot Γ h, SimpleGraph.reachable_bot]

/-! ## The graph of [II, (4.16)] -/

section Instances

/-- The graph `𝒢₀ = ∑_x G_{b₁b₂} Q_x(Θ_{ax} G_{xb₁} Ḡ_{xb₂})` of [II, (4.16)] with `×`-dotted
edges `b₁ ≠ b₂`, `x ≠ b₁`, `x ≠ b₂` (external atoms `a, b₁, b₂ = 0, 1, 2`, internal atom `x`). -/
private def qGraph0 : Graph 3 1 :=
  ⟨[mkC (.G .plus) (.inl 1) (.inl 2), mkC .xdot (.inl 1) (.inl 2),
    mkC (.theta []) (.inl 0) (.inr 0), (mkC (.G .plus) (.inr 0) (.inl 1)).labelQ (.inr 0),
    (mkC (.G .minus) (.inr 0) (.inl 2)).labelQ (.inr 0), mkC .xdot (.inr 0) (.inl 1),
    mkC .xdot (.inr 0) (.inl 2)], 1⟩

end Instances

/-! ## The clause on `⊗` -/

/-- The clause on `⊗` on an output graph `t` of `Γ`: if every component of `Γ` at `⊗` is a diffusive
edge, the components of `t` at `⊗` are, up to order, the images of those of `Γ` (in particular
no dotted or `×`-dotted edge is at `⊗`). -/
def Tracked.QOtimes {n : ℕ} (Γ : Graph 3 n) (t : Tracked 3 n) : Prop :=
  (∀ c ∈ Γ.comps, (c.x = .inl 0 ∨ c.y = .inl 0) → c.kind.isDiffusive = true) →
    (t.g.comps.filter fun c => decide (c.x = .inl 0 ∨ c.y = .inl 0)).Perm
      ((Γ.comps.filter fun c => decide (c.x = .inl 0 ∨ c.y = .inl 0)).map (Comp.map t.f))

/-- The clauses `qExpansionOut` of [II, Lemma 4.15] on an output graph `t`, with the clause
on `⊗` (`Tracked.QOtimes`). -/
def qExpansionOut' {n : ℕ} (D C' : ℕ) (x : Atom 3 n) (Γ : Graph 3 n) (t : Tracked 3 n) : Prop :=
  qExpansionOut D C' x Γ t ∧ t.QOtimes Γ

end RBM8D.Graphs
