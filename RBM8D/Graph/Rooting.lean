import RBM8D.Graph.MolRead
import RBM8D.Graph.Local.Dot

/-!
# Graph clauses on the external atoms, the dotted edges and the labels

Clauses on a graph with external atoms `⊗ = 0`, `⊕ = 1`, `⊖ = 2` that [II, Def 6.3] carries and
that [II, Lemma 6.5] and [II, (8.18)–(8.24)] read:

* every component at `⊗` is diffusive; the dotted edges form a forest; `⊕` and `⊖` lie in one
  dotted block; the graph is a `⊕`-recollision graph at `𝔟₁ = 𝔟₂`; the graph is rooted at the
  external atoms ([II, (8.33)–(8.42)]); with their decision procedures;
* no dotted or `×`-dotted edge carries a `P`/`Q` label; no internal atom, or some internal atom
  has a waved, diffusive or dotted edge to an external atom ([II, Lemma 6.5 (4), (5)]).
-/

namespace RBM8D.Graphs

/-- Every component at `⊗` is a diffusive edge, so that the graph is `Σ_x Θ_{𝔞x} (𝒢₀)_{x𝔟}` with a
plain or labelled `Θ` edge ([II, (8.18)] and the line after it). -/
def Graph.TensorDiffusive {n : ℕ} (Γ : Graph 3 n) : Prop :=
  Γ.comps.all (fun c => !(c.x == .inl 0 || c.y == .inl 0) || c.kind.isDiffusive) = true

/-- The dotted edges form a forest without loops: their number plus the number of dotted blocks
is the number of atoms. -/
def Graph.DotsAcyclic {k n : ℕ} (Γ : Graph k n) : Prop :=
  (Γ.comps.filter fun c => decide (c.kind = .dot)).length +
    (dotBlocks (allAtoms k n) Γ.comps).length = k + n

/-- `⊕` and `⊖` lie in one dotted block. -/
def Graph.pmBlockB {n : ℕ} (Γ : Graph 3 n) : Bool :=
  (dotBlocks (allAtoms 3 n) Γ.comps).any fun B => B.contains (.inl 1) && B.contains (.inl 2)

/-- `⊕` and `⊖` lie in one dotted block. -/
def Graph.PMBlock {n : ℕ} (Γ : Graph 3 n) : Prop := Γ.pmBlockB = true

/-- The graph is a `⊕`-recollision graph at `𝔟₁ = 𝔟₂`: the dotted block of `⊕` or of `⊖`
contains an internal atom, so that the graph with `⊕ = ⊖ = 𝔟` has a dotted edge at `𝔟` in its
block normal form ([II, (8.20)–(8.21)]). -/
def Graph.DiagRecoll {n : ℕ} (Γ : Graph 3 n) : Prop :=
  ((dotBlocks (allAtoms 3 n) Γ.comps).any fun B =>
    (B.contains (.inl 1) || B.contains (.inl 2)) && B.any fun u => u.isRight) = true

/-- The graph is rooted at the external atoms `⊗, ⊕, ⊖`: the properties (3)–(4) of the auxiliary
graph of the count [II, (8.33)–(8.42)] in the proof of [II, Claim 8.6], for a graph with an
internal atom that is not a `⊕`-recollision graph at `𝔟₁ = 𝔟₂`.
* `⊗`: some diffusive edge joins `⊗` to an internal or identified atom, and every diffusive edge at
  `⊗` does (the `Θ` edge at `⊗` ends at an internal atom);
* `⊕`: a solid edge of charge `+` (blue) joins `⊕` to an internal atom, or some diffusive edge
  joins `⊕` to an internal or identified atom;
* `⊖`: a solid edge of charge `−` (red) joins `⊖` to an internal atom, or some diffusive edge
  joins `⊖` to an internal or identified atom. -/
def Graph.RootedAtExt {n : ℕ} (Γ : Graph 3 n) : Prop :=
  (Γ.HasDiffToPinned (.inl 0) ∧ Γ.DiffToPinned (.inl 0)) ∧
  ((∃ c ∈ Γ.comps, c.kind = .G .plus ∧
      (c.x = .inl 1 ∧ c.y.isRight = true ∨ c.y = .inl 1 ∧ c.x.isRight = true)) ∨
    Γ.HasDiffToPinned (.inl 1)) ∧
  ((∃ c ∈ Γ.comps, c.kind = .G .minus ∧
      (c.x = .inl 2 ∧ c.y.isRight = true ∨ c.y = .inl 2 ∧ c.x.isRight = true)) ∨
    Γ.HasDiffToPinned (.inl 2))

instance {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.TensorDiffusive :=
  inferInstanceAs (Decidable (_ = true))

instance {k n : ℕ} (Γ : Graph k n) : Decidable Γ.DotsAcyclic :=
  inferInstanceAs (Decidable (_ = _))

instance {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.PMBlock :=
  inferInstanceAs (Decidable (_ = true))

instance {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.DiagRecoll :=
  inferInstanceAs (Decidable (_ = true))

instance {n : ℕ} (Γ : Graph 3 n) : Decidable Γ.RootedAtExt := by
  unfold Graph.RootedAtExt Graph.HasDiffToPinned Graph.DiffToPinned; infer_instance

/-- No dotted or `×`-dotted edge carries a `P`/`Q` label. -/
def Graph.NoLabDot {k n : ℕ} (Γ : Graph k n) : Prop :=
  ∀ c ∈ Γ.comps, (c.kind = .dot ∨ c.kind = .xdot) → c.label = none

/-- No internal atom, or some internal atom has a waved, diffusive or dotted edge to an external
atom. On a normal regular graph this is equivalent to: every internal atom is joined to `⊗`, `⊕`
or `⊖` by a path of waved, diffusive and dotted edges; the graphs substituted in
[II, Lemma 6.5 (4), (5)] need it for the normal regular form of the substituted graphs. -/
def Graph.RgCheck {n : ℕ} (Γ : Graph 3 n) : Prop :=
  n = 0 ∨ ∃ c ∈ Γ.comps, (c.kind.joinsMol = true ∨ c.kind.isDiffusive = true) ∧
    (c.x.isRight = true ∧ c.y.isLeft = true ∨ c.x.isLeft = true ∧ c.y.isRight = true)

end RBM8D.Graphs
