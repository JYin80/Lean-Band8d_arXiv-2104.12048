module

public import RBM8D.Graph.QExp.Step3
public import RBM8D.Graph.Local.DotNorm

@[expose] public section

/-!
# The third step of the `Q`-expansions with deterministic choices

[II, Lemma 4.14], with [II, (4.17)–(4.21)], for a function of the graph: `selStep3 d x Γ` makes
every choice of [II, §4.4, Step 3] at the first index, in the printed order, on a graph
`Γ = Γ_ω P_x(𝒢)`: the splits `1 = 1_{u = x} + 1_{u ≠ x}` of the atoms of the factors of `𝒢` not
yet `×`-dotted to `x`, [II, (4.17)] on every factor of `𝒢` one by one, the removal of the label
`P_x` when every factor of `𝒢` carries the minor `{x}`, [II, (4.20)], [II, (4.21)], the removal of
the `×`-dotted edges without solid edge, and `O_merge` on every graph other than the leading term
`Γ_ω 𝒢`. Every step is a term of an operator of `QElemStep`; every term before `O_merge` has the
identity map. The Taylor degree `d` of [II, (4.21)] is the only numeric parameter.

The main statement is `selStep3_clauses'`: the clauses of [II, Lemma 4.14] on every output graph for
every error order `D ≤ ord Γ + d`, the components at the external atoms, the three forms of the
output graphs (the leading term with the identity map; a strictly higher paper scaling order; a
paper scaling order at least that of `Γ` plus `d + 1`), and the history of every output graph
(`SelStep3Hist`): a chain of steps of the run (`SelStep3Step`), each an elementary step with the
identity map, then `O_merge` and removals of redundant dotted edges (`SelStep3Drop`). The steps of
the phases are `selStep3_split_step`, `selStep3_schur_step`, `selStep3_dropP_step`,
`selStep3_rev_step`, `selStep3_taylor_step` and `selStep3_clean_step`.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-! ## The run of [II, Lemma 4.14] with deterministic choices -/

section SelStep3Run

variable {k : ℕ}

open Classical in
/-- The index of the first dotted edge of `L` whose ends are joined by the other dotted edges of
`L`. -/
def selStep3_firstRed {n : ℕ} (L : List (Comp (Atom k n))) : Option ℕ :=
  (List.range L.length).find? fun i =>
    decide (∃ c, L[i]? = some c ∧ c.kind = .dot ∧ (step3_dg (L.eraseIdx i)).Reachable c.x c.y)

/-- `r` times: the first dotted edge whose ends are joined by the other dotted edges is removed. -/
def selStep3_drop {n : ℕ} : ℕ → Graph k n → Graph k n
  | 0, g => g
  | r + 1, g =>
    match selStep3_firstRed g.comps with
    | some i => selStep3_drop r ⟨g.comps.eraseIdx i, g.coeff⟩
    | none => g

/-- The last step of the run for an input of scaling order `o`: a graph of scaling order at most
`o` (the leading term `𝒢`) is kept as it is; on the other graphs `O_merge`, then the removal of
redundant dotted edges until the dot excess is that of `T`. -/
def selStep3_final {n : ℕ} (o : ℤ) (T : Graph k n) : TExpansion k n :=
  if T.ord ≤ o then [Tracked.self T] else
    match T.mergeT with
    | some t => [⟨t.nOut, selStep3_drop (step3_eL t.g.comps - step3_eL T.comps).toNat t.g, t.f⟩]
    | none => []

open Classical in
/-- The phase of the `×`-dotted edges without solid edge: at the first one,
`1_{u ≠ v} = 1 - 1_{u = v}`; a term with a `×`-dotted edge inside a block is dropped; with
fuel `0` or no such edge, the last step. -/
def selStep3_clean (o : ℤ) : ℕ → {n : ℕ} → Graph k n → TExpansion k n
  | 0, _, T => selStep3_final o T
  | m + 1, _, T =>
    match T.comps.findIdx? (step3_badB T.comps) with
    | some i => (oXdotT i T).bind fun _ g => if g.XdotApart then selStep3_clean o m g else []
    | none => selStep3_final o T

/-- The phase of [II, (4.21)] with Taylor degree `d`: at the first weight `(G_{xx})⁻¹`; with
fuel `0` or no such weight, the phase of the `×`-dotted edges without solid edge. -/
def selStep3_taylor (o : ℤ) (d : ℕ) : ℕ → {n : ℕ} → Graph k n → TExpansion k n
  | 0, _, T => selStep3_clean o (step3_nBad T.comps) T
  | m + 1, _, T =>
    match T.comps.findIdx? fun c => c.kind.isInvB with
    | some i => (oTaylorT d i T).bind fun _ g => selStep3_taylor o d m g
    | none => selStep3_clean o (step3_nBad T.comps) T

/-- [II, (4.20)] at the component with index `i`: at a weight or light weight, `oSchurWRevT`;
otherwise `oSchurRevT`. -/
def selStep3_revAt {n : ℕ} (X : Atom k n) (i : ℕ) (T : Graph k n) : TExpansion k n :=
  match (T.comps[i]?).map Comp.kind with
  | some (.weight _) | some (.light _) => oSchurWRevT X i T
  | _ => oSchurRevT X i T

/-- [II, (4.17)] at the component with index `i`: at a weight or light weight, `oSchurWT`;
otherwise `oSchurT`. -/
def selStep3_schurAt {n : ℕ} (X : Atom k n) (i : ℕ) (T : Graph k n) : TExpansion k n :=
  match (T.comps[i]?).map Comp.kind with
  | some (.weight _) | some (.light _) => oSchurWT X i T
  | _ => oSchurT X i T

/-- The phase of [II, (4.20)]: at the first component with a minor; with fuel `0` or no such
component, the phase of [II, (4.21)]. -/
def selStep3_rev (o : ℤ) (d : ℕ) : ℕ → {n : ℕ} → Atom k n → Graph k n → TExpansion k n
  | 0, _, _, T => selStep3_taylor o d (step3_nInv T.comps) T
  | m + 1, _, X, T =>
    match T.comps.findIdx? fun c => !c.minor.isEmpty with
    | some i => (selStep3_revAt X i T).bind fun f g => selStep3_rev o d m (f X) g
    | none => selStep3_taylor o d (step3_nInv T.comps) T

/-- Every labelled weight or edge has the minor `{X}`, and some component carries the label
`P_X`. -/
def selStep3_AllMinor {n : ℕ} (X : Atom k n) (T : Graph k n) : Prop :=
  (∀ c ∈ T.comps, c.label.isSome = true → c.kind.isRandom = true → c.minor = [X]) ∧
    ∃ c ∈ T.comps, c.label = some (.P, X)

open Classical in
/-- If every labelled weight or edge has the minor `{X}`, the label `P_X` is removed
(`Graph.dropLabels`); then the phase of [II, (4.20)]. -/
def selStep3_dropP (o : ℤ) (d : ℕ) {n : ℕ} (X : Atom k n) (T : Graph k n) : TExpansion k n :=
  if selStep3_AllMinor X T then selStep3_rev o d (step3_nMin T.dropLabels.comps) X T.dropLabels
  else selStep3_rev o d (step3_nMin T.comps) X T

/-- The phase of [II, (4.17)]: at the first pending component; with fuel `0` or no pending
component, `selStep3_dropP`. -/
def selStep3_schur (o : ℤ) (d : ℕ) : ℕ → {n : ℕ} → Atom k n → Graph k n → TExpansion k n
  | 0, _, X, T => selStep3_dropP o d X T
  | m + 1, _, X, T =>
    match T.comps.findIdx? (step3_pendB X) with
    | some i => (selStep3_schurAt X i T).bind fun f g => selStep3_schur o d m (f X) g
    | none => selStep3_dropP o d X T

open Classical in
/-- The splits `1 = 1_{u = X} + 1_{u ≠ X}` at the atoms `us` in order, each atom already
`×`-dotted to `X` skipped: the term with the dotted edge goes to the phase of the `×`-dotted
edges without solid edge (and is dropped if it has a `×`-dotted edge inside a block), the term
with the `×`-dotted edge goes on; after the last atom, the phase of [II, (4.17)]. -/
def selStep3_split (o : ℤ) (d : ℕ) {n : ℕ} (X : Atom k n) :
    List (Atom k n) → Graph k n → TExpansion k n
  | [], T => selStep3_schur o d (step3_nPend X T.comps) X T
  | u :: us, T =>
    if HasX T.comps u X then selStep3_split o d X us T else
      (if (⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n).XdotApart then
        selStep3_clean o (step3_nBad (T.comps ++ [mkC .dot u X]))
          ⟨T.comps ++ [mkC .dot u X], T.coeff⟩
      else []) ++ selStep3_split o d X us ⟨T.comps ++ [mkC .xdot u X], T.coeff⟩

/-- The atoms of the labelled weights and edges of `Γ`, in the order of the components. -/
def selStep3_us {n : ℕ} (Γ : Graph k n) : List (Atom k n) :=
  (Γ.comps.filter fun c => c.label.isSome && c.kind.isRandom).flatMap fun c => [c.x, c.y]

open Classical in
/-- The expansion of [II, Lemma 4.14] of a graph `Γ = Γ_ω P_X(𝒢)` with Taylor degree `d`, with
every choice made by the first index: no term if `Γ` has a `×`-dotted edge inside a block;
otherwise the splits of the atoms of `𝒢` against `X`, [II, (4.17)] on every factor of `𝒢` one by
one, the removal of the label `P_X`, [II, (4.20)], [II, (4.21)], the removal of the `×`-dotted
edges without solid edge, and `O_merge` on the graphs of scaling order above that of `Γ`. The
choices do not depend on `d`, which enters only through [II, (4.21)]. -/
def selStep3 (d : ℕ) {n : ℕ} (X : Atom k n) (Γ : Graph k n) : TExpansion k n :=
  if Γ.XdotApart then selStep3_split Γ.ord d X (selStep3_us Γ) Γ else []

end SelStep3Run

/-! ## The steps of the run as elementary steps -/

section SelStep3Hist

variable {k n : ℕ}

/-- One step of the run `selStep3 d` at the internal atom `X`, from `T` to `g`, with the identity
atom map: `g` is a term of a split `1 = 1_{u = X} + 1_{u ≠ X}` (`oSplitT`), of [II, (4.17)]
(`oSchurT`, `oSchurWT`), of [II, (4.20)] (`oSchurRevT`, `oSchurWRevT`), of [II, (4.21)] with
Taylor degree `d` (`oTaylorT`), of `1_{u ≠ v} = 1 - 1_{u = v}` (`oXdotT`), or `g` is `T` with the
label `P_X` removed (`Graph.dropLabels`) when every labelled component has `X` in its minor. -/
inductive SelStep3Step (d : ℕ) (X : Atom k n) : Graph k n → Graph k n → Prop
  | split (u : Atom k n) (T g : Graph k n) (h : Tracked.self g ∈ oSplitT u X T) :
      SelStep3Step d X T g
  | schur (i : ℕ) (T g : Graph k n) (h : Tracked.self g ∈ oSchurT X i T) : SelStep3Step d X T g
  | schurW (i : ℕ) (T g : Graph k n) (h : Tracked.self g ∈ oSchurWT X i T) :
      SelStep3Step d X T g
  | dropP (T : Graph k n) (hP : T.IsPFormAt X)
      (hm : ∀ c ∈ T.comps, c.label.isSome = true → X ∈ c.minor) :
      SelStep3Step d X T T.dropLabels
  | schurRev (i : ℕ) (T g : Graph k n) (h : Tracked.self g ∈ oSchurRevT X i T) :
      SelStep3Step d X T g
  | schurWRev (i : ℕ) (T g : Graph k n) (h : Tracked.self g ∈ oSchurWRevT X i T) :
      SelStep3Step d X T g
  | taylor (i : ℕ) (T g : Graph k n) (h : Tracked.self g ∈ oTaylorT d i T) :
      SelStep3Step d X T g
  | xdot (i : ℕ) (T g : Graph k n) (h : Tracked.self g ∈ oXdotT i T) : SelStep3Step d X T g

/-- A step of the run at an internal atom is an elementary step `QElemStep`. -/
theorem SelStep3Step.qElemStep {d : ℕ} {X : Atom k n} (hX : X.isRight = true) {T g : Graph k n}
    (h : SelStep3Step d X T g) : QElemStep ⟨n, T⟩ ⟨n, g⟩ := by
  cases h with
  | split u T g h => exact QElemStep.split u X T (Tracked.self g) hX h
  | schur i T g h => exact QElemStep.schur X i T (Tracked.self g) hX h
  | schurW i T g h => exact QElemStep.schurW X i T (Tracked.self g) hX h
  | dropP T hP hm => exact QElemStep.dropP X T hP hm
  | schurRev i T g h => exact QElemStep.schurRev X i T (Tracked.self g) hX h
  | schurWRev i T g h => exact QElemStep.schurWRev X i T (Tracked.self g) hX h
  | taylor i T g h => exact QElemStep.taylor d i T (Tracked.self g) h
  | xdot i T g h => exact QElemStep.xdot i T (Tracked.self g) h

/-- A graph of [II, (4.17)] at the component with index `i`, as chosen by the run, is a step of
the run. -/
theorem SelStep3Step.of_schurAt {d : ℕ} {X : Atom k n} {i : ℕ} {T g : Graph k n}
    (h : Tracked.self g ∈ selStep3_schurAt X i T) : SelStep3Step d X T g := by
  unfold selStep3_schurAt at h
  split at h
  · exact .schurW i T g h
  · exact .schurW i T g h
  · exact .schur i T g h

/-- A graph of [II, (4.20)] at the component with index `i`, as chosen by the run, is a step of
the run. -/
theorem SelStep3Step.of_revAt {d : ℕ} {X : Atom k n} {i : ℕ} {T g : Graph k n}
    (h : Tracked.self g ∈ selStep3_revAt X i T) : SelStep3Step d X T g := by
  unfold selStep3_revAt at h
  split at h
  · exact .schurWRev i T g h
  · exact .schurWRev i T g h
  · exact .schurRev i T g h

/-- The removal of a dotted edge of `g` whose ends are joined by the other dotted edges. -/
def SelStep3Drop {m : ℕ} (g g' : Graph k m) : Prop :=
  ∃ i c, g.comps[i]? = some c ∧ c.kind = .dot ∧
    (⟨g.comps.eraseIdx i, g.coeff⟩ : Graph k m).SameBlock c.x c.y ∧
    g' = ⟨g.comps.eraseIdx i, g.coeff⟩

/-- The removal of a redundant dotted edge is an elementary step `QElemStep` (`dropDot`). -/
theorem SelStep3Drop.qElemStep {m : ℕ} {g g' : Graph k m} (h : SelStep3Drop g g') :
    QElemStep ⟨m, g⟩ ⟨m, g'⟩ := by
  obtain ⟨i, c, hc, hk, hb, rfl⟩ := h
  exact QElemStep.dropDot i g c hc hk hb

/-- A chain of removals of redundant dotted edges is a chain of elementary steps. -/
theorem SelStep3Drop.chain {m : ℕ} {g g' : Graph k m}
    (h : Relation.ReflTransGen SelStep3Drop g g') :
    Relation.ReflTransGen QElemStep ⟨m, g⟩ ⟨m, g'⟩ :=
  h.lift (fun g => (⟨m, g⟩ : Σ n, Graph k n)) fun _ _ h => h.qElemStep

/-- The history of an output graph `t` of the run `selStep3 d` of `Γ` at `X`: a chain of steps of
the run from `Γ` to a graph `T`, and `t` is `T` with the identity map, or `t` is obtained from the
output of `O_merge` at `T` by removals of redundant dotted edges, with the atom map of `O_merge`. -/
def SelStep3Hist (d : ℕ) (X : Atom k n) (Γ : Graph k n) (t : Tracked k n) : Prop :=
  ∃ T : Graph k n, Relation.ReflTransGen (SelStep3Step d X) Γ T ∧
    (t = Tracked.self T ∨ ∃ t₀ : Tracked k n, T.mergeT = some t₀ ∧
      ∃ g' : Graph k t₀.nOut, Relation.ReflTransGen SelStep3Drop t₀.g g' ∧
        t = ⟨t₀.nOut, g', t₀.f⟩)

end SelStep3Hist

/-! ## The steps of the phases -/

section SelStep3Steps

variable {k n : ℕ}

/-- The leading term `𝒢` has the scaling order of `Γ`. -/
theorem selStep3_lead_ord {X : Atom k n} {Γ T : Graph k n} (h : LeadPerm X Γ T) :
    T.ord = Γ.ord := by
  obtain ⟨us, -, hp⟩ := h
  have h1 := (hp.map fun c => c.kind.ord).sum_eq
  simp only [List.map_map, List.map_append, List.sum_append] at h1
  have h2 : (us.map ((fun c : Comp (Atom k n) => c.kind.ord) ∘ fun u => mkC .xdot u X)).sum =
      0 :=
    List.sum_eq_zero fun a ha => by
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 ha
      rfl
  have h3 : ∀ L : List (Comp (Atom k n)),
      (L.map ((fun c => c.kind.ord) ∘ baseC)) = L.map fun c => c.kind.ord := fun L => rfl
  rw [h2, add_zero, h3, h3] at h1
  unfold Graph.ord
  rw [h1]

/-- One step of [II, (4.20)] at a component with minor `{X}`: the operator gives two graphs,
both keeping the clauses `Base`, the components at the external atoms and the class, with one
component with a minor fewer. -/
theorem selStep3_rev_step {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hG : GIn Γ)
    (hB : Base D' S X Γ T) (hK : OK1 Γ T) (hcls : Cls D' X Γ T) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hm : c.minor = [X]) :
    ∃ Gs : List (Graph k n), selStep3_revAt X i T = Gs.map Tracked.self ∧ Gs.length = 2 ∧
      TExpansion.ValueEq (Gs.map Tracked.self) T modelAdm ∧
      ∀ g ∈ Gs, (Base D' S X Γ g ∧ Cls D' X Γ g ∧ step3_nMin g.comps + 1 = step3_nMin T.comps ∧
        nWD g.comps = nWD T.comps) ∧ OK1 Γ g := by
  have hcT : c ∈ T.comps := List.mem_of_getElem? hc
  obtain ⟨-, ⟨ch, hk⟩, hx, hy, -, -⟩ := (hB.minor c hcT).resolve_left (by rw [hm]; simp)
  have hgg := goodGroup_of hB c hcT
  have hcd : c.kind.isDiffusive = false := by
    rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
  have hOK : ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩], OK1 Γ g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hK.replace hc hcd _ (fun d hd o ho => by rw [List.mem_singleton.1 hd] at ho; exact ho) _
    · refine hK.replace hc hcd _ (fun d hd o ho => ?_) _
      simp only [revNew, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · exact atO_of_ends hB.xright ho (Or.inl rfl) (Or.inr (Or.inr rfl))
      · exact atO_of_ends hB.xright ho (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
      · exact atO_of_ends hB.xright ho (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl))
  rcases hk with hk | hk
  · have hE := oSchurRevT_eq X hc hk hm hgg hx hy
    have hSel : selStep3_revAt X i T = oSchurRevT X i T := by simp [selStep3_revAt, hc, hk]
    have hst : ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n),
        ⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩], QElemStep ⟨n, T⟩ ⟨n, g⟩ :=
      fun g hg => QElemStep.schurRev X i T (Tracked.self g) hB.xright
        (by rw [hE]; exact List.mem_map_of_mem hg)
    refine ⟨[(⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩], hSel.trans hE, rfl, ?_,
      fun g hg => ⟨rev_common hG hB hcls hc hm (Or.inl hk) hst g hg, hOK g hg⟩⟩
    intro Ω ι _ _ PF D₀ hA e
    have := oSchurRev_value k n X i Ω ι PF D₀ hA T e
    unfold oSchurRev at this
    rw [hE] at this
    exact this
  · have hyx : c.y = c.x := (hB.wf c hcT).1 (by rcases hk with hk | hk <;> rw [hk] <;> rfl)
    have hE := oSchurWRevT_eq X hc hk hm hgg hx hyx
    have hSel : selStep3_revAt X i T = oSchurWRevT X i T := by
      rcases hk with hk | hk <;> simp [selStep3_revAt, hc, hk]
    have hst : ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n),
        ⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩], QElemStep ⟨n, T⟩ ⟨n, g⟩ :=
      fun g hg => QElemStep.schurWRev X i T (Tracked.self g) hB.xright
        (by rw [hE]; exact List.mem_map_of_mem hg)
    refine ⟨[(⟨T.comps.eraseIdx i ++ [{ c with minor := [] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, -T.coeff⟩], hSel.trans hE, rfl, ?_,
      fun g hg => ⟨rev_common hG hB hcls hc hm (Or.inr hk) hst g hg, hOK g hg⟩⟩
    intro Ω ι _ _ PF D₀ hA e
    have := step1_oSchurWRev_value k n X i Ω ι PF D₀ hA T e
    simp only at this
    rw [hE] at this
    exact this

/-- One step of [II, (4.17)] at a pending component: the operator gives two graphs, both keeping
the clauses `Base`, the components at the external atoms and the class, with one pending
component fewer. -/
theorem selStep3_schur_step {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hΓ : Γ.Plain)
    (hB : Base D' S X Γ T) (hK : OK1 Γ T) (hP : Step3PendInv X Γ T)
    (hcls : ClsP D' X Γ T ∨ AllPendL X Γ T) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hp : step3_pendB X c = true) :
    ∃ Gs : List (Graph k n), selStep3_schurAt X i T = Gs.map Tracked.self ∧ Gs.length = 2 ∧
      TExpansion.ValueEq (Gs.map Tracked.self) T modelAdm ∧
      ∀ g ∈ Gs, (Base D' S X Γ g ∧ Step3PendInv X Γ g ∧ (ClsP D' X Γ g ∨ AllPendL X Γ g) ∧
        step3_nPend X g.comps + 1 = step3_nPend X T.comps) ∧ OK1 Γ g := by
  have hcT : c ∈ T.comps := List.mem_of_getElem? hc
  obtain ⟨hcΓ, -, -⟩ := hP c hcT hp
  have hpp := hp
  simp only [step3_pendB, Bool.and_eq_true, List.isEmpty_iff, bne_iff_ne, ne_eq] at hpp
  obtain ⟨⟨⟨⟨-, hcr⟩, hm⟩, hx⟩, hy⟩ := hpp
  have hl := goodGroup_of hB c hcT
  obtain ⟨ch, hk⟩ := kind_of_plain_random (hΓ c hcΓ) hcr
  have hcd : c.kind.isDiffusive = false := by
    rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
  have hOK : ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩], OK1 Γ g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hK.replace hc hcd _ (fun d hd o ho => by rw [List.mem_singleton.1 hd] at ho; exact ho) _
    · refine hK.replace hc hcd _ (fun d hd o ho => ?_) _
      simp only [revNew, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · exact atO_of_ends hB.xright ho (Or.inl rfl) (Or.inr (Or.inr rfl))
      · exact atO_of_ends hB.xright ho (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
      · exact atO_of_ends hB.xright ho (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl))
  rcases hk with hk | hk
  · have hE := oSchurT_eq X hc hk hm hl hx hy
    have hSel : selStep3_schurAt X i T = oSchurT X i T := by simp [selStep3_schurAt, hc, hk]
    have hst : ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n),
        ⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩], QElemStep ⟨n, T⟩ ⟨n, g⟩ :=
      fun g hg => QElemStep.schur X i T (Tracked.self g) hB.xright
        (by rw [hE]; exact List.mem_map_of_mem hg)
    refine ⟨[(⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩], hSel.trans hE, rfl, ?_,
      fun g hg => ⟨schur_common hB hP hcls hc hp (Or.inl hk) hst g hg, hOK g hg⟩⟩
    intro Ω ι _ _ PF D₀ hA e
    have := oSchur_value k n X i Ω ι PF D₀ hA T e
    unfold oSchur at this
    rw [hE] at this
    exact this
  · have hyx : c.y = c.x := (hB.wf c hcT).1 (by rcases hk with hk | hk <;> rw [hk] <;> rfl)
    have hE := oSchurWT_eq X hc hk hm hl hx hyx
    have hSel : selStep3_schurAt X i T = oSchurWT X i T := by
      rcases hk with hk | hk <;> simp [selStep3_schurAt, hc, hk]
    have hst : ∀ g ∈ [(⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n),
        ⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩], QElemStep ⟨n, T⟩ ⟨n, g⟩ :=
      fun g hg => QElemStep.schurW X i T (Tracked.self g) hB.xright
        (by rw [hE]; exact List.mem_map_of_mem hg)
    refine ⟨[(⟨T.comps.eraseIdx i ++ [{ c with minor := [X] }], T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ revNew X c ch, T.coeff⟩], hSel.trans hE, rfl, ?_,
      fun g hg => ⟨schur_common hB hP hcls hc hp (Or.inr hk) hst g hg, hOK g hg⟩⟩
    intro Ω ι _ _ PF D₀ hA e
    have := step1_oSchurW_value k n X i Ω ι PF D₀ hA T e
    simp only at this
    rw [hE] at this
    exact this

/-- The removal of the label `P_X` decided on the graph: with no pending component left, the
test `selStep3_AllMinor` holds exactly for the graphs of the form of the leading term
(`AllPendL`); there the label is removed (the step `dropP`) and the result has the class of the
leading term; otherwise a labelled weight or edge is attached to the block of `X` (`ClsP`). -/
theorem selStep3_dropP_step {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hB : Base D' S X Γ T)
    (hK : OK1 Γ T) (hnp : step3_nPend X T.comps = 0) (hcls : ClsP D' X Γ T ∨ AllPendL X Γ T) :
    (selStep3_AllMinor X T → QElemStep ⟨n, T⟩ ⟨n, T.dropLabels⟩ ∧
        Base D' S X Γ T.dropLabels ∧ OK1 Γ T.dropLabels ∧ ClsLead X Γ T.dropLabels ∧
        TExpansion.ValueEq [Tracked.self T.dropLabels] T modelAdm) ∧
      (¬ selStep3_AllMinor X T → ClsP D' X Γ T) := by
  have hpend : ∀ c ∈ T.comps, step3_pendB X c = false := by
    intro c hc
    by_contra h
    have : c ∈ T.comps.filter (step3_pendB X) := List.mem_filter.2 ⟨hc, by simpa using h⟩
    have := List.length_pos_of_mem this
    unfold step3_nPend at hnp
    omega
  refine ⟨fun hA => ?_, fun hA => ?_⟩
  · have hA' : AllPendL X Γ T := by
      rcases hcls with ⟨⟨e, he, hel, her, hem, -⟩, -⟩ | h
      · exfalso
        have := hA.1 e he (by rw [hel]; rfl) her
        rw [hem] at this
        cases this
      · exact h
    obtain ⟨hB', hL, hv⟩ := dropP_step hB hnp hA'
    refine ⟨?_, hB', hK.dropLabels fun c hc => (hB.wf c hc).2, hL, hv⟩
    refine QElemStep.dropP X T ⟨hA.2, hB.lab⟩ fun c hc hl => ?_
    rw [hA.1 c hc hl ((hB.wf c hc).2 hl)]
    exact List.mem_singleton_self X
  · rcases hcls with h | ⟨h1, h2, -⟩
    · exact h
    · exfalso
      refine hA ⟨fun c hc hl hr => ?_, h2⟩
      rcases h1 c hc hl hr with h | h
      · rw [hpend c hc] at h; cases h
      · exact h

/-- One step of [II, (4.21)] at a weight `(G_{xx})⁻¹` with Taylor degree `D'`: the operator gives
`D' + 2` graphs, each keeping the clauses `Base`, the components at the external atoms and the
class, with one weight `(G_{xx})⁻¹` fewer. -/
theorem selStep3_taylor_step {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hG : GIn Γ)
    (hB : Base D' S X Γ T) (hK : OK1 Γ T) (hmin : ∀ c ∈ T.comps, c.minor = [])
    (hcls : Cls D' X Γ T) {i : ℕ} {c : Comp (Atom k n)}
    (hc : T.comps[i]? = some c) (hci : c.kind.isInvB = true) :
    ∃ Gs : List (Graph k n), oTaylorT D' i T = Gs.map Tracked.self ∧ Gs.length = D' + 2 ∧
      TExpansion.ValueEq (Gs.map Tracked.self) T modelAdm ∧
      ∀ g ∈ Gs, Base D' S X Γ g ∧ OK1 Γ g ∧ (∀ c ∈ g.comps, c.minor = []) ∧
        Cls D' X Γ g ∧ step3_nInv g.comps + 1 = step3_nInv T.comps := by
  have hcT : c ∈ T.comps := List.mem_of_getElem? hc
  have hi : i < T.comps.length := (List.getElem?_eq_some_iff.1 hc).1
  obtain ⟨ch, hk⟩ : ∃ ch, c.kind = .inv ch := by
    revert hci
    cases c.kind <;> simp [Kind.isInvB]
  obtain ⟨hcx, hcy, hcm⟩ := hB.inv c hcT hci
  -- the guard of `oTaylorT`
  have hguard : (c.label.all fun ℓ => T.GoodGroup ℓ &&
      (T.comps.eraseIdx i).any fun c' => decide (c'.label = some ℓ)) = true := by
    rcases hB.lab c hcT with hl | hl
    · rw [hl]; rfl
    · rw [hl]
      simp only [Option.all_some, Bool.and_eq_true, Graph.GoodGroup, List.all_eq_true,
        List.any_eq_true, decide_eq_true_eq]
      refine ⟨fun d hd => ?_, ?_⟩
      · by_cases hdl : d.label = some (.P, X)
        · simp [hB.good d hd (by rw [hdl]; rfl)]
        · simp [hdl]
      · rcases hcls with ⟨⟨w, hw, hwl, -, -, hwi, -⟩, -⟩ | ⟨hlf, -⟩ | ⟨hlf, -⟩
        · refine ⟨w, mem_eraseIdx_of_ne hc hw ?_, hwl⟩
          rintro rfl
          rw [hci] at hwi
          cases hwi
        · rw [hlf c hcT] at hl
          cases hl
        · rw [hlf c hcT] at hl
          cases hl
  have hE := oTaylorT_eq D' hc hk hguard
  set Lw : Comp (Atom k n) := { c with kind := .light ch, y := c.x } with hLw
  set W : Comp (Atom k n) := { c with kind := .wD ch D', y := c.x } with hW
  set Gs : List (Graph k n) := ((List.range (D' + 1)).map fun j' =>
      (⟨T.comps.eraseIdx i ++ List.replicate j' Lw,
        (-1 : Coeff) ^ j' * mInvOf ch ^ (j' + 1) * T.coeff⟩ : Graph k n)) ++
      [(⟨T.comps.eraseIdx i ++ [W], T.coeff⟩ : Graph k n)] with hGs
  have hv : TExpansion.ValueEq (Gs.map Tracked.self) T modelAdm := by
    intro Ω ι _ _ PF D₀ hA e
    have := oTaylor_value k n D' i Ω ι PF D₀ hA T e
    unfold oTaylor at this
    rw [hE] at this
    exact this
  have hlen : Gs.length = D' + 2 := by simp [hGs]
  refine ⟨Gs, hE, hlen, hv, fun g hg => ?_⟩
  have hstep : QElemStep ⟨n, T⟩ ⟨n, g⟩ :=
    QElemStep.taylor D' i T (Tracked.self g) (by rw [hE]; exact List.mem_map_of_mem hg)
  have hcr : c.kind.isRandom = true := by rw [hk]; rfl
  have hcxy : c.x = c.y := hcx.trans hcy.symm
  have hcp : step3_pendB X c = false := by simp [step3_pendB, hcx]
  have hcmin : (!c.minor.isEmpty) = false := by simp [hcm]
  have hlwp : step3_pendB X Lw = false := by simp [step3_pendB, hLw, hcx]
  have hwp : step3_pendB X W = false := by simp [step3_pendB, hW, hcx]
  -- common facts on the new components
  have hT₀ : ∀ (new : List (Comp (Atom k n))) (co : Coeff),
      (∀ d ∈ new, d = Lw ∨ d = W) →
      QElemStep ⟨n, T⟩ ⟨n, ⟨T.comps.eraseIdx i ++ new, co⟩⟩ →
      Γ.ord + (D' + 1) * (nWD (T.comps.eraseIdx i ++ new) : ℤ) ≤
        (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).ord →
      sizeΦ D' X (T.comps.eraseIdx i ++ new) ≤ S →
      T.ord - (D' + 1) * (nWD T.comps : ℤ) ≤
        (⟨T.comps.eraseIdx i ++ new, co⟩ : Graph k n).ord -
        (D' + 1) * (nWD (T.comps.eraseIdx i ++ new) : ℤ) →
      Base D' S X Γ ⟨T.comps.eraseIdx i ++ new, co⟩ ∧ OK1 Γ ⟨T.comps.eraseIdx i ++ new, co⟩ ∧
        (∀ c ∈ T.comps.eraseIdx i ++ new, c.minor = []) ∧
        Cls D' X Γ ⟨T.comps.eraseIdx i ++ new, co⟩ := by
    intro new co hnew hst hord hsz hord'
    have hfx : ∀ d ∈ T.comps.eraseIdx i ++ new, d ∈ T.comps ∨ d = Lw ∨ d = W := by
      intro d hd
      rcases List.mem_append.1 hd with h | h
      · exact Or.inl (List.mem_of_mem_eraseIdx h)
      · exact Or.inr (hnew d h)
    have hB' : Base D' S X Γ ⟨T.comps.eraseIdx i ++ new, co⟩ := by
      refine step3_base_replace hB hc new co hst hcr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        (by linarith) hsz
      · intro d hd
        rcases hnew d hd with rfl | rfl <;> simp [hLw, hW, Kind.isRandom]
      · rw [hcxy]
      · intro d hd hds
        rcases hnew d hd with rfl | rfl <;> simp [Kind.isSolid] at hds
      · intro hG
        rw [hk] at hG
        cases hG
      · intro d hd
        have hwc := hB.wf c hcT
        rcases hnew d hd with rfl | rfl <;>
          exact ⟨fun _ => rfl, fun _ => by simp [hLw, hW, Kind.isRandom]⟩
      · intro d hd
        rcases hnew d hd with rfl | rfl <;> exact hB.lab c hcT
      · intro h
        have := (hG.plain c (mem_carryL h).1).2.1 ch
        exact this hk
      · intro d hd _
        rcases hnew d hd with rfl | rfl <;> simp [hLw, hW, Comp.isGoodKind, hcm]
      · intro d hd
        rcases hnew d hd with rfl | rfl <;> exact Or.inl hcm
      · intro d hd hdi
        rcases hnew d hd with rfl | rfl <;> simp [Kind.isInvB] at hdi
      · intro d hd _
        rcases hnew d hd with rfl | rfl <;> exact hcm
    refine ⟨hB', hK.replace hc (by rw [hk]; rfl) new (fun d hd o ho => by
      rcases hnew d hd with rfl | rfl <;> exact atO_of_xx ho rfl rfl) co, ?_, ?_⟩
    · intro d hd
      rcases hfx d hd with h | rfl | rfl
      · exact hmin d h
      · exact hcm
      · exact hcm
    · refine step3_cls_replace hcls ?_ ?_ ?_ ?_ (by push_cast at hord' ⊢; linarith)
      · intro hL
        have := lead_inv hG hL.2 hcT
        rw [hci] at this
        cases this
      · intro d hd _ _ hdi _
        refine List.mem_append_left _ (mem_eraseIdx_of_ne hc hd ?_)
        rintro rfl
        rw [hci] at hdi
        cases hdi
      · intro u v h
        have hdots : ((T.comps.eraseIdx i ++ new).filter fun c => decide (c.kind = .dot)).Perm
            (T.comps.filter fun c => decide (c.kind = .dot)) := by
          rw [filter_dot_append (fun d hd => by rcases hnew d hd with rfl | rfl <;> simp)]
          exact filter_dot_eraseIdx hc (by rw [hk]; simp)
        change (step3_dg (T.comps.eraseIdx i ++ new)).Reachable u v
        rw [(dg_eL_of_filter_perm hdots).1]
        exact h
      · intro hlf d hd
        rcases hfx d hd with h | rfl | rfl
        · exact hlf d h
        · exact hlf c hcT
        · exact hlf c hcT
  -- the counts
  have hcnt : ∀ (new : List (Comp (Atom k n))), (∀ d ∈ new, d = Lw ∨ d = W) →
      sizeΦ D' X (T.comps.eraseIdx i ++ new) + (D' + 1) + 1 ≤
        sizeΦ D' X T.comps + new.length ∧
      step3_nInv (T.comps.eraseIdx i ++ new) + 1 = step3_nInv T.comps := by
    intro new hnew
    have hp := count_replace hc new (step3_pendB X)
    have hm' := count_replace hc new (fun c => !c.minor.isEmpty)
    have hi' := count_replace hc new (fun c => c.kind.isInvB)
    have hlen' : (T.comps.eraseIdx i ++ new).length + 1 = T.comps.length + new.length := by
      rw [List.length_append, List.length_eraseIdx_of_lt hi]
      have := List.length_pos_of_mem hcT
      omega
    have e1 : new.filter (step3_pendB X) = [] := List.filter_eq_nil_iff.2 fun d hd => by
      rcases hnew d hd with rfl | rfl <;> simp [hlwp, hwp]
    have e2 : new.filter (fun c => !c.minor.isEmpty) = [] :=
      List.filter_eq_nil_iff.2 fun d hd => by
      rcases hnew d hd with rfl | rfl <;> simp [hLw, hW, hcm]
    have e3 : new.filter (fun c => c.kind.isInvB) = [] := List.filter_eq_nil_iff.2 fun d hd => by
      rcases hnew d hd with rfl | rfl <;> simp [hLw, hW, Kind.isInvB]
    rw [e1, hcp] at hp
    rw [e2, hcmin] at hm'
    rw [e3, hci] at hi'
    simp only [List.length_nil, add_zero, Bool.false_eq_true, ite_false, ite_true] at hp hm' hi'
    unfold sizeΦ step3_nPend step3_nMin step3_nInv
    refine ⟨?_, hi'⟩
    rw [hp, hm']
    nlinarith [hi']
  have hord0 := ord_replace hc
  have hcord : c.kind.ord = 0 := by rw [hk]; rfl
  rw [hGs, List.mem_append, List.mem_map, List.mem_singleton] at hg
  rcases hg with ⟨j', hj', rfl⟩ | rfl
  · have hj'' : j' ≤ D' := by simp at hj'; omega
    have hnew : ∀ d ∈ List.replicate j' Lw, d = Lw ∨ d = W :=
      fun d hd => Or.inl (List.eq_of_mem_replicate hd)
    obtain ⟨h1, h2⟩ := hcnt _ hnew
    have hnw : nWD (T.comps.eraseIdx i ++ List.replicate j' Lw) = nWD T.comps := by
      have := count_replace hc (List.replicate j' Lw) (fun c => c.kind.step3_isWDB)
      have e : (List.replicate j' Lw).filter (fun c => c.kind.step3_isWDB) = [] :=
        List.filter_eq_nil_iff.2 fun d hd => by
          rw [List.eq_of_mem_replicate hd]; simp [hLw, Kind.step3_isWDB]
      rw [e, hk] at this
      unfold nWD
      have h2 : (Kind.inv ch).step3_isWDB = false := rfl
      simp only [h2, Bool.false_eq_true, ite_false, add_zero, List.length_nil] at this
      exact this
    have hordj : (⟨T.comps.eraseIdx i ++ List.replicate j' Lw,
        (-1 : Coeff) ^ j' * mInvOf ch ^ (j' + 1) * T.coeff⟩ : Graph k n).ord = T.ord + j' := by
      rw [hord0, hcord]
      simp [hLw, Kind.ord, List.map_replicate, List.sum_replicate]
    have hBo := hB.ord
    have hBs := hB.size
    refine (fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, h2⟩) (hT₀ _ _ hnew hstep ?_ ?_ ?_)
    · rw [hordj, hnw]
      linarith
    · simp only [List.length_replicate] at h1
      omega
    · rw [hordj, hnw]
      linarith
  · have hnew : ∀ d ∈ [W], d = Lw ∨ d = W := fun d hd => Or.inr (List.mem_singleton.1 hd)
    obtain ⟨h1, h2⟩ := hcnt _ hnew
    have hnw : nWD (T.comps.eraseIdx i ++ [W]) = nWD T.comps + 1 := by
      have := count_replace hc [W] (fun c => c.kind.step3_isWDB)
      rw [hk] at this
      unfold nWD
      have h2 : (Kind.inv ch).step3_isWDB = false := rfl
      have h3 : ([W] : List (Comp (Atom k n))).filter (fun c => c.kind.step3_isWDB) = [W] := by
        simp [hW, Kind.step3_isWDB]
      simp only [h2, h3, Bool.false_eq_true, ite_false, add_zero, List.length_singleton] at this
      exact this
    have hordW : (⟨T.comps.eraseIdx i ++ [W], T.coeff⟩ : Graph k n).ord = T.ord + (D' + 1) := by
      rw [hord0, hcord]
      simp [hW, Kind.ord]
    have hBo := hB.ord
    have hBs := hB.size
    refine (fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, h2⟩) (hT₀ _ _ hnew hstep ?_ ?_ ?_)
    · rw [hordW, hnw]
      push_cast
      linarith
    · simp only [List.length_singleton] at h1
      omega
    · rw [hordW, hnw]
      push_cast
      linarith

/-- One step of `1_{u ≠ v} = 1 - 1_{u = v}` at a `×`-dotted edge without solid edge: the operator
gives the graph without that edge and the graph with a dotted edge in its place; each of them
without `×`-dotted edge inside a block keeps the clauses `Base`, the components at the external
atoms and the class, with one such `×`-dotted edge fewer, and the first one has no `×`-dotted
edge inside a block. -/
theorem selStep3_clean_step {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hG : GIn Γ)
    (hB : Base D' S X Γ T) (hK : OK1 Γ T) (hmin : ∀ c ∈ T.comps, c.minor = [])
    (hinv : ∀ c ∈ T.comps, c.kind.isInvB = false) (hcls : Cls D' X Γ T)
    {i : ℕ} {c : Comp (Atom k n)} (hc : T.comps[i]? = some c) (hb : step3_badB T.comps c = true) :
    oXdotT i T = [(⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n),
        ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩].map Tracked.self ∧
      TExpansion.ValueEq ([(⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n),
        ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩].map Tracked.self) T modelAdm ∧
      (⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n).XdotApart ∧
      ∀ g ∈ [(⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n),
        ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩],
        (∀ d ∈ g.comps, (d.kind = .dot ∨ d.kind = .xdot) → d.label = none) ∧
        (g.XdotApart → Base D' S X Γ g ∧ OK1 Γ g ∧ (∀ c ∈ g.comps, c.minor = []) ∧
          (∀ c ∈ g.comps, c.kind.isInvB = false) ∧ Cls D' X Γ g ∧
          step3_nBad g.comps + 1 ≤ step3_nBad T.comps) := by
  have hcT : c ∈ T.comps := List.mem_of_getElem? hc
  have hcb := hb
  simp only [step3_badB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hcb
  obtain ⟨hk, hsj⟩ := hcb
  have hns : ¬ HasS T.comps c.x c.y := by
    rw [← solidJoinB_iff, hsj]
    simp
  have hdotlab := dotlab_of_wf hB.wf
  have hcl : c.label = none := hdotlab c hcT (Or.inr hk)
  have hE := step3_oXdotT_eq hc hk hcl hsj
  have hsame1 : ∀ d, d.kind.isSolid = true → (d ∈ T.comps ↔ d ∈ T.comps.eraseIdx i) := by
    intro d hd
    refine ⟨fun h => mem_eraseIdx_of_ne hc h (fun h' => ?_), List.mem_of_mem_eraseIdx⟩
    rw [h', hk] at hd
    simp [Kind.isSolid] at hd
  have hcnt : step3_nBad T.comps =
      ((T.comps.eraseIdx i).filter (step3_badB T.comps)).length + 1 := by
    unfold step3_nBad
    rw [length_filter_eraseIdx hc (step3_badB T.comps)]
    simp [step3_badB, hk, hsj]
  have hb1 : step3_nBad (T.comps.eraseIdx i) + 1 ≤ step3_nBad T.comps := by
    unfold step3_nBad
    rw [List.filter_congr (fun d _ => (badB_congr hsame1 d).symm)]
    unfold step3_nBad at hcnt
    omega
  have hsame2 : ∀ d, d.kind.isSolid = true →
      (d ∈ T.comps ↔ d ∈ T.comps.eraseIdx i ++ [mkC .dot c.x c.y]) := by
    intro d hd
    rw [hsame1 d hd, List.mem_append, List.mem_singleton]
    constructor
    · exact Or.inl
    · rintro (h | rfl)
      · exact h
      · simp [mkC, Kind.isSolid] at hd
  have hb2 : step3_nBad (T.comps.eraseIdx i ++ [mkC .dot c.x c.y]) + 1 ≤ step3_nBad T.comps := by
    unfold step3_nBad
    rw [List.filter_congr (fun d _ => (badB_congr hsame2 d).symm), List.filter_append]
    simp only [List.length_append]
    have : ([mkC .dot c.x c.y] : List (Comp (Atom k n))).filter (step3_badB T.comps) = [] := by
      simp [step3_badB, mkC]
    rw [this]
    simp only [List.length_nil, add_zero]
    unfold step3_nBad at hcnt
    omega
  have hv : TExpansion.ValueEq ([(⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n),
      ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩].map Tracked.self) T modelAdm := by
    intro Ω ι _ _ PF D₀ _ e
    have := step1_oXdot_value k n i Ω ι PF D₀ trivial T e
    simp only [hE] at this
    exact this
  have hrandk : ∀ d ∈ T.comps, d.kind.isRandom = true → d ≠ c := by
    rintro d hd hdr rfl
    rw [hk] at hdr
    cases hdr
  have hstep1 : QElemStep ⟨n, T⟩ ⟨n, ⟨T.comps.eraseIdx i, T.coeff⟩⟩ :=
    QElemStep.xdot i T (Tracked.self ⟨T.comps.eraseIdx i, T.coeff⟩) (by rw [hE]; simp)
  have hD1 := clean_drop hB hmin hc hk hns hstep1
  refine ⟨by rw [hE]; rfl, hv, hD1.1.xapart, ?_⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · refine ⟨fun d hd hdk => hdotlab d (List.mem_of_mem_eraseIdx hd) hdk, fun _ => ?_⟩
    obtain ⟨hB', hsb, hord, hnw, hin⟩ := hD1
    refine ⟨hB', hK.erase hc (by rw [hk]; rfl) T.coeff,
      fun d hd => hmin d (List.mem_of_mem_eraseIdx hd),
      fun d hd => hinv d (List.mem_of_mem_eraseIdx hd), ?_, hb1⟩
    rcases hcls with hP | hLF | hL
    · rcases cls_clean (Or.inl hP)
        (fun d hd hdr => mem_eraseIdx_of_ne hc hd (hrandk d hd hdr))
        (fun d hd => Or.inl (List.mem_of_mem_eraseIdx hd)) (fun u v h => (hsb u v).2 h)
        hord.ge hnw with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases cls_clean (Or.inr hLF)
        (fun d hd hdr => mem_eraseIdx_of_ne hc hd (hrandk d hd hdr))
        (fun d hd => Or.inl (List.mem_of_mem_eraseIdx hd)) (fun u v h => (hsb u v).2 h)
        hord.ge hnw with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨fun d hd => hL.1 d (List.mem_of_mem_eraseIdx hd),
        (lead_erase hG hL.2 hc hk hns T.coeff).1⟩)
  · have hstep : QElemStep ⟨n, T⟩ ⟨n, ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩⟩ :=
      QElemStep.xdot i T (Tracked.self ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩)
        (by rw [hE]; simp)
    refine ⟨?_, fun hxa => ?_⟩
    · intro d hd hdk
      rcases List.mem_append.1 hd with h | h
      · exact hdotlab d (List.mem_of_mem_eraseIdx h) hdk
      · rw [List.mem_singleton.1 h]
        rfl
    obtain ⟨hB', hsb, hord, hnw, hin⟩ := clean_dot hB hmin hc hk hns hstep hxa
    have hfx : ∀ d ∈ T.comps.eraseIdx i ++ [mkC .dot c.x c.y],
        d ∈ T.comps.eraseIdx i ∨ d = mkC .dot c.x c.y := by
      intro d hd
      rcases List.mem_append.1 hd with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_singleton.1 h)
    have hkeep : ∀ d ∈ T.comps, d.kind.isRandom = true →
        d ∈ T.comps.eraseIdx i ++ [mkC .dot c.x c.y] := fun d hd hdr =>
      List.mem_append_left _ (mem_eraseIdx_of_ne hc hd (hrandk d hd hdr))
    have hlab : ∀ d ∈ T.comps.eraseIdx i ++ [mkC .dot c.x c.y],
        d ∈ T.comps ∨ d.label = none := by
      intro d hd
      rcases hfx d hd with h | rfl
      · exact Or.inl (List.mem_of_mem_eraseIdx h)
      · exact Or.inr rfl
    refine ⟨hB', hK.replace hc (by rw [hk]; rfl) _
      (fun d hd o ho => by rw [List.mem_singleton.1 hd] at ho; exact ho) _, ?_, ?_, ?_, hb2⟩
    · intro d hd
      rcases hfx d hd with h | rfl
      · exact hmin d (List.mem_of_mem_eraseIdx h)
      · rfl
    · intro d hd
      rcases hfx d hd with h | rfl
      · exact hinv d (List.mem_of_mem_eraseIdx h)
      · rfl
    · rcases hcls with hP | hLF | hL
      · rcases cls_clean (Or.inl hP) hkeep hlab hsb (by rw [hord]; linarith) hnw with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rcases cls_clean (Or.inr hLF) hkeep hlab hsb (by rw [hord]; linarith) hnw with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · -- the leading term with `u` identified with `X`
        obtain ⟨-, hy, hu⟩ := lead_erase hG hL.2 hc hk hns T.coeff
        obtain ⟨e, he, hel, her, hem, hei, hue⟩ := lead_witness hG hL.2 hmin hL.1 hu
        refine Or.inr (Or.inl ⟨?_, ⟨e, hkeep e he her, hel, her, hem, hei, c.x, hue, ?_⟩, ?_⟩)
        · intro d hd
          rcases hlab d hd with h | h
          · exact hL.1 d h
          · exact h
        · rw [← hy]
          exact step3_dg_reach_of_mem (L := T.comps.eraseIdx i ++ [mkC .dot c.x c.y])
            (c := mkC .dot c.x c.y) (List.mem_append_right _ (List.mem_singleton_self _)) rfl
        · rw [hord, hnw]
          have := hB.ord
          linarith

/-- One split `1 = 1_{u = X} + 1_{u ≠ X}` at an atom `u` of a labelled weight or edge of `Γ` not
`×`-dotted to `X`, when `𝒢` has no weight or edge attached to the block of `X` and the blocks of
`T` are those of `Γ`: the operator gives the graph with the dotted edge `u = X` and the graph
with the `×`-dotted edge `u ≠ X`. The first one, if it has no `×`-dotted edge inside a block,
keeps the clauses `Base` and the components at the external atoms and has a labelled weight or
edge attached to the block of `X` (`ClsP`); the second one has no `×`-dotted edge inside a block,
keeps the clauses `Base`, the components at the external atoms and the blocks. -/
theorem selStep3_split_step {D' S : ℕ} {X : Atom k n} {Γ T : Graph k n} (hG : GIn Γ)
    (hfree : Γ.LabelledFreeAtBlock X) (hB : Base D' S X Γ T) (hK : OK1 Γ T)
    (hsz : sizeΦ D' X T.comps + 1 ≤ S) (hdg : step3_dg T.comps = step3_dg Γ.comps)
    (hsub : ∀ g ∈ Γ.comps, g ∈ T.comps)
    {u : Atom k n} {c₀ : Comp (Atom k n)} (hc₀ : c₀ ∈ Γ.comps) (hl₀ : c₀.label.isSome = true)
    (hr₀ : c₀.kind.isRandom = true) (hu₀ : u ∈ [c₀.x, c₀.y]) :
    oSplitT u X T = [(⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n),
        ⟨T.comps ++ [mkC .xdot u X], T.coeff⟩].map Tracked.self ∧
      TExpansion.ValueEq ([(⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n),
        ⟨T.comps ++ [mkC .xdot u X], T.coeff⟩].map Tracked.self) T modelAdm ∧
      (∀ d ∈ T.comps ++ [mkC .dot u X], (d.kind = .dot ∨ d.kind = .xdot) → d.label = none) ∧
      ((⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n).XdotApart →
        Base D' S X Γ ⟨T.comps ++ [mkC .dot u X], T.coeff⟩ ∧
        OK1 Γ ⟨T.comps ++ [mkC .dot u X], T.coeff⟩ ∧
        ClsP D' X Γ ⟨T.comps ++ [mkC .dot u X], T.coeff⟩) ∧
      Base D' S X Γ ⟨T.comps ++ [mkC .xdot u X], T.coeff⟩ ∧
      OK1 Γ ⟨T.comps ++ [mkC .xdot u X], T.coeff⟩ ∧
      step3_dg (T.comps ++ [mkC .xdot u X]) = step3_dg Γ.comps := by
  have hnb : ¬ T.SameBlock u X := by
    have h := hfree c₀ hc₀ hl₀ hr₀
    change ¬ (step3_dg T.comps).Reachable u X
    rw [hdg]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu₀
    rcases hu₀ with rfl | rfl
    · exact h.1
    · exact h.2
  have huX : u ≠ X := fun h => hnb (by rw [h]; exact SimpleGraph.Reachable.refl _)
  have hnO : ∀ κ, ∀ o, Step3ODiff o Γ → ∀ d ∈ [mkC κ u X], step3_atO o d = false := by
    intro κ o hO d hd
    rw [List.mem_singleton.1 hd]
    exact split_atO hB.xright hO hc₀ hr₀ hu₀ κ
  have hE := step3_oSplitT_eq (T := T) huX
  have hv : TExpansion.ValueEq ([(⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n),
      ⟨T.comps ++ [mkC .xdot u X], T.coeff⟩].map Tracked.self) T modelAdm := by
    intro Ω ι _ _ PF D₀ _ e
    have := step1_oSplit_value k n u X Ω ι PF D₀ trivial T e
    simp only at this
    rw [hE] at this
    exact this
  have hstep : ∀ g ∈ [(⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n),
      ⟨T.comps ++ [mkC .xdot u X], T.coeff⟩], QElemStep ⟨n, T⟩ ⟨n, g⟩ := fun g hg =>
    QElemStep.split u X T (Tracked.self g) hB.xright (by rw [hE]; exact List.mem_map_of_mem hg)
  have hdg' : step3_dg (T.comps ++ [mkC .xdot u X]) = step3_dg T.comps := by
    apply dg_congr
    intro e he
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | rfl)
      · exact h
      · simp [mkC] at he
    · exact Or.inl
  have hxa : (⟨T.comps ++ [mkC .xdot u X], T.coeff⟩ : Graph k n).XdotApart := by
    intro d hd hdk hb
    have hb' : T.SameBlock d.x d.y := by
      change (step3_dg T.comps).Reachable d.x d.y
      rw [← hdg']
      exact hb
    rcases List.mem_append.1 hd with h | h
    · exact hB.xapart d h hdk hb'
    · rw [List.mem_singleton.1 h] at hb'
      exact hnb hb'
  obtain ⟨hB₂, -, -⟩ := step3_base_append hB (Or.inr rfl) hnb (hstep _ (by simp)) hxa
    (by rw [sizeΦ_append_xdot _ (Or.inr rfl)]; exact hsz)
  refine ⟨hE, hv, ?_, fun hxa₁ => ?_, hB₂, hK.append _ (hnO .xdot) _, hdg'.trans hdg⟩
  · intro d hd hdk
    rcases List.mem_append.1 hd with h | h
    · exact dotlab_of_wf hB.wf d h hdk
    · rw [List.mem_singleton.1 h]; rfl
  obtain ⟨hB₁, hord, hnw⟩ := step3_base_append hB (Or.inl rfl) hnb (hstep _ (by simp)) hxa₁
    (by rw [sizeΦ_append_xdot _ (Or.inl rfl)]; exact hsz)
  have hc₀T : c₀ ∈ T.comps := hsub c₀ hc₀
  have hl₀' : c₀.label = some (.P, X) := by
    rcases hB.lab c₀ hc₀T with h | h
    · rw [h] at hl₀; cases hl₀
    · exact h
  refine ⟨hB₁, hK.append _ (hnO .dot) _, ⟨c₀, List.mem_append_left _ hc₀T, hl₀', hr₀,
    (hG.plain c₀ hc₀).1, ?_, u, hu₀, ?_⟩, ?_⟩
  · have := (hG.plain c₀ hc₀).2.1
    revert this
    cases c₀.kind <;> simp [Kind.isInvB]
  · exact step3_dg_reach_of_mem (L := T.comps ++ [mkC .dot u X]) (c := mkC .dot u X)
      (List.mem_append_right _ (List.mem_singleton_self _)) rfl
  · rw [hord, hnw]
    have := hB.ord
    simp only [Kind.ord]
    linarith

end SelStep3Steps

/-! ## Expansions with a given list of terms -/

section SelStep3DExp

variable {k n : ℕ}

/-- `F` has the value of `Γ`, at most `B` terms, and every term has the property `P`. -/
private def DExp (P : Tracked k n → Prop) (B : ℕ) (Γ : Graph k n) (F : TExpansion k n) : Prop :=
  F.ValueEq Γ modelAdm ∧ F.length ≤ B ∧ ∀ t ∈ F, P t

private theorem DExp.mono {P : Tracked k n → Prop} {B B' : ℕ} {Γ : Graph k n}
    {F : TExpansion k n} (h : DExp P B Γ F) (hB : B ≤ B') : DExp P B' Γ F :=
  ⟨h.1, h.2.1.trans hB, h.2.2⟩

/-- A graph of value `0` is the value of the empty sum. -/
private theorem DExp.nil {P : Tracked k n → Prop} (B : ℕ) {Γ : Graph k n}
    (h : ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
      (e : Fin k → ι), Γ.valR PF D e = 0) : DExp P B Γ [] := by
  refine ⟨?_, by simp, by simp⟩
  intro Ω ι _ _ PF D _ e
  rw [h]
  funext ω
  simp [TExpansion.forget, Expansion.valR]

/-- If a formal sum of graphs with the identity maps has the value of `Γ`, and each of its graphs
`g` is the value of `R g`, then `Γ` is the value of the concatenation of the `R g`. -/
private theorem DExp.bind {P : Tracked k n → Prop} {B : ℕ} {Γ : Graph k n}
    (Gs : List (Graph k n)) (R : Graph k n → TExpansion k n)
    (hv : TExpansion.ValueEq (Gs.map Tracked.self) Γ modelAdm)
    (h : ∀ g ∈ Gs, DExp P B g (R g)) : DExp P (Gs.length * B) Γ (Gs.flatMap R) := by
  have key : ∀ Gs : List (Graph k n), (∀ g ∈ Gs, DExp P B g (R g)) →
      (∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι),
        modelAdm Ω ι PF D → ∀ e : Fin k → ι,
          (TExpansion.forget (Gs.flatMap R)).valR PF D e =
            fun ω => (Gs.map fun g => g.valR PF D e ω).sum) ∧
        (Gs.flatMap R).length ≤ Gs.length * B ∧ ∀ t ∈ Gs.flatMap R, P t := by
    intro Gs
    induction Gs with
    | nil =>
      intro _
      refine ⟨fun _ _ _ _ _ _ _ _ => ?_, by simp, by simp⟩
      funext ω
      simp [TExpansion.forget, Expansion.valR]
    | cons g Gs ih =>
      intro h
      obtain ⟨h1, h2, h3⟩ := h g (List.mem_cons_self ..)
      obtain ⟨h4, h5, h6⟩ := ih fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
      refine ⟨?_, ?_, ?_⟩
      · intro Ω ι _ _ PF D hA e
        rw [List.flatMap_cons, forget_append_valR, h1 Ω ι PF D hA e, h4 Ω ι PF D hA e]
        funext ω
        simp
      · simp only [List.flatMap_cons, List.length_append, List.length_cons]
        nlinarith
      · intro t ht
        rw [List.flatMap_cons] at ht
        rcases List.mem_append.1 ht with ht | ht
        · exact h3 t ht
        · exact h6 t ht
  obtain ⟨h1, h2, h3⟩ := key Gs h
  refine ⟨?_, h2, h3⟩
  intro Ω ι _ _ PF D hA e
  rw [h1 Ω ι PF D hA e, ← hv Ω ι PF D hA e]
  funext ω
  simp [TExpansion.forget, Expansion.valR, Tracked.self, Function.comp_def]

/-- The value of `Γ` as the sum of the values of two graphs, each the value of a formal sum. -/
private theorem DExp.append {P : Tracked k n → Prop} {B₁ B₂ : ℕ} {Γ g₁ g₂ : Graph k n}
    {F₁ F₂ : TExpansion k n}
    (hv : TExpansion.ValueEq ([g₁, g₂].map Tracked.self) Γ modelAdm)
    (h₁ : DExp P B₁ g₁ F₁) (h₂ : DExp P B₂ g₂ F₂) : DExp P (B₁ + B₂) Γ (F₁ ++ F₂) := by
  refine ⟨?_, by simp only [List.length_append]; exact Nat.add_le_add h₁.2.1 h₂.2.1, ?_⟩
  · intro Ω ι _ _ PF D hA e
    rw [forget_append_valR, h₁.1 Ω ι PF D hA e, h₂.1 Ω ι PF D hA e, ← hv Ω ι PF D hA e]
    funext ω
    simp [TExpansion.forget, Expansion.valR, Tracked.self]
  · intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · exact h₁.2.2 t ht
    · exact h₂.2.2 t ht

/-- The operator `O` applied to graphs with the identity maps. -/
private theorem selStep3_bind_self (Gs : List (Graph k n))
    (O : ∀ {n' : ℕ}, (Atom k n → Atom k n') → Graph k n' → TExpansion k n') :
    TExpansion.bind (Gs.map Tracked.self) O = Gs.flatMap fun g => O id g := by
  unfold TExpansion.bind
  rw [List.flatMap_map]
  congr 1
  funext g
  simp only [Tracked.self, Function.comp_id]
  exact List.map_id' _

private theorem selStep3_findIdx_some {α : Type*} {L : List α} {p : α → Bool} {i : ℕ}
    (h : L.findIdx? p = some i) : ∃ c, L[i]? = some c ∧ p c = true := by
  obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  exact ⟨L[i], List.getElem?_eq_getElem hi, hp⟩

end SelStep3DExp

/-! ## The removal of the redundant dotted edges -/

section SelStep3DropSec

variable {k m : ℕ}

private theorem selStep3_firstRed_some {L : List (Comp (Atom k m))} {i : ℕ}
    (h : selStep3_firstRed L = some i) :
    ∃ c, L[i]? = some c ∧ c.kind = .dot ∧ (step3_dg (L.eraseIdx i)).Reachable c.x c.y := by
  unfold selStep3_firstRed at h
  simpa using List.find?_some h

private theorem selStep3_firstRed_none {L : List (Comp (Atom k m))}
    (h : selStep3_firstRed L = none) {i : ℕ} {c : Comp (Atom k m)} (hc : L[i]? = some c)
    (hk : c.kind = .dot) : ¬ (step3_dg (L.eraseIdx i)).Reachable c.x c.y := by
  unfold selStep3_firstRed at h
  rw [List.find?_eq_none] at h
  intro hr
  have hi : i < L.length := (List.getElem?_eq_some_iff.1 hc).1
  exact h i (List.mem_range.2 hi) (by simpa using ⟨c, hc, hk, hr⟩)

/-- The facts on `selStep3_drop r g` when `r` dotted edges are redundant. -/
private def DropSpec (e₀ : ℤ) (r : ℕ) (g g' : Graph k m) : Prop :=
  Relation.ReflTransGen SelStep3Drop g g' ∧ step3_eL g'.comps = e₀ ∧
    g'.ord = g.ord - 2 * r ∧ g'.coeff = g.coeff ∧ g'.comps.Sublist g.comps ∧
    (∀ d ∈ g.comps, d.kind ≠ .dot → d ∈ g'.comps) ∧
    (g'.comps.filter fun d => !decide (d.kind = .dot)).Perm
      (g.comps.filter fun d => !decide (d.kind = .dot)) ∧
    (∀ u v, g'.SameBlock u v ↔ g.SameBlock u v) ∧
    (g.Step3DCS .plus → g'.Step3DCS .plus) ∧ (g.ConnNoX → g'.ConnNoX) ∧
    g'.wavedThetaGraph = g.wavedThetaGraph ∧
    ((∀ d ∈ g.comps, d.kind = .dot → d.label = none) →
      ∀ (Ω ι : Type) [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι)
        (e : Fin k → ι), g'.valR PF D e = g.valR PF D e)

/-- Removing `r` times the first redundant dotted edge brings the dot excess down to `e₀`; the
components other than dotted edges are kept with their multiplicities. -/
private theorem selStep3_drop_spec (e₀ : ℤ) (he₀ : 0 ≤ e₀) :
    ∀ (r : ℕ) (g : Graph k m), step3_eL g.comps = e₀ + r → DropSpec e₀ r g (selStep3_drop r g)
  | 0, g, h => show DropSpec e₀ 0 g g from
      ⟨Relation.ReflTransGen.refl, by simpa using h, by simp, rfl,
      List.Sublist.refl _, fun _ hd _ => hd, List.Perm.refl _, fun _ _ => Iff.rfl, id, id, rfl,
      fun _ _ _ _ _ _ _ _ => rfl⟩
  | r + 1, g, h => by
    obtain ⟨i₀, c₀, hc₀, hk₀, hr₀⟩ :=
      step3_exists_red_of_pos (L := g.comps) (by push_cast at h; omega)
    obtain ⟨i, hi⟩ : ∃ i, selStep3_firstRed g.comps = some i := by
      rcases h' : selStep3_firstRed g.comps with _ | i
      · exact absurd hr₀ (selStep3_firstRed_none h' hc₀ hk₀)
      · exact ⟨i, rfl⟩
    obtain ⟨c, hc, hk, hr⟩ := selStep3_firstRed_some hi
    have hdrop : selStep3_drop (r + 1) g = selStep3_drop r ⟨g.comps.eraseIdx i, g.coeff⟩ := by
      simp only [selStep3_drop, hi]
    rw [hdrop]
    obtain ⟨-, he, hord, hmem, hfp, hb, hdc, hconn, hwt⟩ := step3_drop_one g hc hk hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h6', h7, h8, h9, h10, h11⟩ :=
      selStep3_drop_spec e₀ he₀ r ⟨g.comps.eraseIdx i, g.coeff⟩ (by push_cast at h; omega)
    refine ⟨Relation.ReflTransGen.head ⟨i, c, hc, hk, hr, rfl⟩ h1, h2, ?_, h4,
      h5.trans (List.eraseIdx_sublist _ _),
      fun d hd hdk => h6 d (hmem d hd hdk) hdk, h6'.trans hfp, fun u v => (h7 u v).trans (hb u v),
      fun hg => h8 (hdc hg), fun hg => h9 (hconn hg), h10.trans hwt, ?_⟩
    · push_cast
      linarith
    · intro hlab Ω ι _ _ PF D e
      rw [h11 (fun d hd hdk => hlab d (List.mem_of_mem_eraseIdx hd) hdk) Ω ι PF D e]
      exact step1_dropDot_value g hc hk hr hlab Ω ι PF D e

end SelStep3DropSec

/-! ## The clauses on the output graphs -/

section SelStep3Phases

variable {k n : ℕ}

/-- The clauses of [II, Lemma 4.14] without the error order: the leading term is the input with its
labels removed, with the identity map; in the last alternative the scaling order is at least that
of `Γ` plus `d + 1`; with the components at the external atoms kept and the history of the
output graph. -/
private def SelOut3 (C' d : ℕ) (X : Atom k n) (Γ : Graph k n) (t : Tracked k n) : Prop :=
  t.QBase C' X Γ ∧ t.Carries Γ ∧ (∀ u, t.IsNew u → t.g.wavedGraph.Reachable (t.f X) u) ∧
    ((∃ T : Graph k n, t = Tracked.self T ∧ T.comps.Perm Γ.dropLabels.comps) ∨
      (t.g.Plain ∧ Γ.ord + 1 ≤ t.g.ord ∧
        ((t.g.LabelFree ∧ ¬ t.g.UnlabelledFreeAtBlock (t.f X)) ∨
          (t.g.IsPFormAt (t.f X) ∧ ¬ t.g.LabelledFreeAtBlock (t.f X)))) ∨
      (Γ.ord + d + 1 ≤ t.g.ord ∧ t.g.Clean)) ∧ Step3OO1 Γ t ∧ SelStep3Hist d X Γ t

/-- The last step for the leading term: the graph itself, without `O_merge`. -/
private theorem selStep3_final_lead {d S C' : ℕ} {X : Atom k n} {Γ T : Graph k n} (hG : GIn Γ)
    (hB : Base d S X Γ T) (hK : OK1 Γ T) (hmin : ∀ c ∈ T.comps, c.minor = [])
    (hN2 : ∀ c ∈ T.comps, c.kind = .xdot → HasS T.comps c.x c.y)
    (hL : ClsLead X Γ T) (hC : k + n + S ≤ C')
    (hH : Relation.ReflTransGen (SelStep3Step d X) Γ T) :
    DExp (SelOut3 C' d X Γ) 1 T (selStep3_final Γ.ord T) := by
  have hfin : selStep3_final Γ.ord T = [Tracked.self T] := by
    simp [selStep3_final, selStep3_lead_ord hL.2]
  rw [hfin]
  have hperm := lead_final hG hL.2 hmin hL.1 hN2
  have hid : ∀ c : Comp (Atom k n), c.map id = c := by
    intro c
    obtain ⟨κ, x, y, m, l⟩ := c
    simp [Comp.map]
  have hcarry : ((carryL Γ).map (Comp.map id)).Subperm T.comps := by
    have e1 : (carryL Γ).map (Comp.map id) = carryL Γ := by
      conv_rhs => rw [← List.map_id (carryL Γ)]
      exact List.map_congr_left fun c _ => hid c
    rw [e1]
    exact hB.carry
  have hNT : T.Normal C' := by
    refine ⟨⟨?_, ?_, hB.internal, fun c hc hk => lead_dot hG hL.2 hc hk⟩,
      fun c hc hk => (hB.solid c hc hk).1, ?_⟩
    · have h3 : T.comps.length ≤ S := le_trans (by unfold sizeΦ; omega) hB.size
      change k + n + T.comps.length ≤ C'
      omega
    · intro u v
      have h := hB.conn u v
      obtain ⟨w⟩ := h
      induction w with
      | nil => exact SimpleGraph.Reachable.refl _
      | cons hadj _ ih =>
        refine SimpleGraph.Reachable.trans ?_ ih
        rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj] at hadj
        refine SimpleGraph.Adj.reachable ?_
        rw [Graph.edgeGraph, SimpleGraph.fromRel_adj]
        obtain ⟨hne, ⟨c, hc, -, h1, h2⟩ | ⟨c, hc, -, h1, h2⟩⟩ := hadj
        · exact ⟨hne, Or.inl ⟨c, hc, h1, h2⟩⟩
        · exact ⟨hne, Or.inr ⟨c, hc, h1, h2⟩⟩
    · intro u v _
      constructor
      · rintro ⟨c, hc, hk, hxy⟩
        obtain ⟨d, hd, hdk, hdxy⟩ := hN2 c hc hk
        refine ⟨d, hd, hdk, ?_⟩
        rcases hdxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
      · rintro ⟨c, hc, hk, hxy⟩
        obtain ⟨-, d, hd, hdk, hdxy⟩ := hB.solid c hc hk
        refine ⟨d, hd, hdk, ?_⟩
        rcases hdxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
  have hord' : Γ.ord ≤ T.ord := by
    have := hB.ord
    have : (0 : ℤ) ≤ ((d + 1 : ℕ) : ℤ) * (nWD T.comps : ℤ) := by positivity
    push_cast at *
    linarith
  have hex : T.dotExcess ≤ Γ.dotExcess := by
    change step3_eL T.comps ≤ step3_eL Γ.comps
    rw [hB.excess]
  refine ⟨?_, by simp, ?_⟩
  · intro Ω ι _ _ PF D₀ _ e
    funext ω
    simp [TExpansion.forget, Expansion.valR, Tracked.self]
  intro t ht
  rw [List.mem_singleton] at ht
  subst ht
  exact ⟨⟨hNT, hord', hB.xapart, hex, hB.xright, fun h => Graph.Step3DCS.doublyConnected (hB.dc h),
    hB.chain⟩, ⟨hcarry, hB.blocks⟩, fun u hu => absurd rfl (hu u), Or.inl ⟨T, rfl, hperm⟩,
    Step3OO1.of_keep hK, T, hH, Or.inl rfl⟩

set_option maxHeartbeats 400000 in
-- The elaboration of this proof needs more than the default number of heartbeats.
/-- The last step for the outputs other than the leading term: `O_merge`, then the removal of
the redundant dotted edges, gives one output graph with the clauses `SelOut3`. -/
private theorem selStep3_final_merge {d S C' : ℕ} {X : Atom k n} {Γ T : Graph k n}
    (hB : Base d S X Γ T) (hK : OK1 Γ T)
    (hmin : ∀ c ∈ T.comps, c.minor = [])
    (hinv : ∀ c ∈ T.comps, c.kind.isInvB = false)
    (hN2 : ∀ c ∈ T.comps, c.kind = .xdot → HasS T.comps c.x c.y)
    (hcls : ClsP d X Γ T ∨ ClsLF d X Γ T) (hC : k + n + S ≤ C')
    (hH : Relation.ReflTransGen (SelStep3Step d X) Γ T) :
    DExp (SelOut3 C' d X Γ) 1 T (selStep3_final Γ.ord T) := by
  have hordc : Γ.ord + 1 + ((d + 1 : ℕ) : ℤ) * (nWD T.comps : ℤ) ≤ T.ord := by
    rcases hcls with ⟨-, h⟩ | ⟨-, -, h⟩ <;> push_cast at h ⊢ <;> linarith
  have hnl : ¬ T.ord ≤ Γ.ord := by
    have : (0 : ℤ) ≤ ((d + 1 : ℕ) : ℤ) * (nWD T.comps : ℤ) := by positivity
    linarith
  -- `O_merge` applies
  have hsol : ∀ c ∈ T.comps, c.kind.isSolid = true → ¬ T.SameBlock c.x c.y := by
    intro c hc hk hb
    obtain ⟨-, d, hd, hdk, hdxy⟩ := hB.solid c hc hk
    apply hB.xapart d hd hdk
    rcases hdxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hb
    · rw [h1, h2]; exact hb.symm
  obtain ⟨t, ht⟩ : ∃ t, T.mergeT = some t := by
    rcases hm : T.mergeT with _ | t
    · obtain ⟨c, hc, hk, hr⟩ := mergeT_none hm
      exact absurd ((T.mrep_eq_iff _ _).1 hr) (hB.xapart c hc hk)
    · exact ⟨t, rfl⟩
  have hs := step3_mergeT_spec ht
  obtain ⟨hord, heL⟩ := hs.ord_eL hsol
  have hle := hs.removedDots_le hB.nonred hB.noloop
  have hlen : t.nOut ≤ n := hs.nOut_le
  set nr := (removedDots T t.f).length with hnr
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = (n : ℤ) - t.nOut - nr := ⟨(n - t.nOut - nr : ℕ), by omega⟩
  have he₀ : 0 ≤ step3_eL T.comps := step3_eL_nonneg _
  have hEq : step3_eL t.g.comps = step3_eL T.comps + r := by rw [heL, hr]; ring
  have hdr : (step3_eL t.g.comps - step3_eL T.comps).toNat = r := by
    rw [hEq, add_sub_cancel_left]
    exact Int.toNat_natCast r
  obtain ⟨hch, hge, hgo, hgc, hsub, hmem', hfp, hblk, hdc, hconn, hwt, hval⟩ :=
    selStep3_drop_spec (step3_eL T.comps) he₀ r t.g hEq
  set g' := selStep3_drop r t.g with hg'
  have hdotlab := dotlab_of_wf hB.wf
  -- the components of `g'`
  have hmc : ∀ c ∈ T.comps, c.kind ≠ .dot →
      step3_mergeComp T.step3_mrep t.f c = some (c.map t.f) := by
    intro c hc hk
    by_cases hks : c.kind.isSolid = true
    · exact step3_mergeComp_of_solid hks fun h => hsol c hc hks ((T.mrep_eq_iff _ _).1 h)
    · exact step3_mergeComp_other hk (by simpa using hks)
  have hin : ∀ c ∈ T.comps, c.kind ≠ .dot → c.map t.f ∈ g'.comps := by
    intro c hc hk
    exact hmem' _ (hs.mem_comps.2 ⟨c, hc, hmc c hc hk⟩) (by simpa [Comp.map] using hk)
  have hout : ∀ c' ∈ g'.comps, ∃ c ∈ T.comps, c' = c.map t.f ∧
      (c.kind = .dot → t.f c.x ≠ t.f c.y) := by
    intro c' hc'
    obtain ⟨c, hc, hm⟩ := hs.mem_comps.1 (hsub.subset hc')
    by_cases hk : c.kind = .dot
    · rw [step3_mergeComp_dot hk] at hm
      split_ifs at hm with hf
      exact ⟨c, hc, (Option.some.inj hm).symm, fun _ => hf⟩
    · rw [hmc c hc hk] at hm
      exact ⟨c, hc, (Option.some.inj hm).symm, fun h => absurd h hk⟩
  have hordg : g'.ord = T.ord := by
    rw [hgo, hord, hr]
    ring
  have hlab1 : T.labels.length ≤ 1 := labels_length_le hB.lab
  -- the output
  have hfin : selStep3_final Γ.ord T = [⟨t.nOut, g', t.f⟩] := by
    simp only [selStep3_final, hnl, ite_false, ht, hdr, hg']
  rw [hfin]
  refine ⟨?_, by simp, ?_⟩
  · intro Ω ι _ _ PF D₀ _ e
    have hm := oMerge_value k n T hlab1 hdotlab Ω ι PF D₀ e
    rw [ht] at hm
    funext ω
    simp only [TExpansion.forget, Expansion.valR, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    rw [hval (fun c hc hk => (hs.hlab hdotlab) c hc (Or.inl hk)) Ω ι PF D₀ e]
    exact congrFun hm ω
  intro t' ht'
  simp only [List.mem_singleton] at ht'
  subst ht'
  obtain ⟨φ, hφ, -⟩ := hs.f_inr
  have hXr : (t.f X).isRight = true := by
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, X = .inr x₀ := by
      rcases hX : X with a | x₀
      · rw [hX] at hB; exact absurd hB.xright (by simp)
      · exact ⟨x₀, rfl⟩
    rw [hx₀, hφ]
    rfl
  -- shape facts of `g'`
  have hClean : g'.Clean := by
    intro c' hc'
    obtain ⟨c, hc, rfl, hdl⟩ := hout c' hc'
    refine ⟨by simp [Comp.map, hmin c hc], ?_, ?_, Comp.map_WF _ (hB.wf c hc)⟩
    · intro ch hch
      have := hinv c hc
      simp only [Comp.map] at hch
      rw [hch] at this
      simp [Kind.isInvB] at this
    · intro hk
      exact hdl hk
  have hnew : ∀ u, ¬ Tracked.IsNew ⟨t.nOut, g', t.f⟩ u := by
    intro u hu
    obtain ⟨v, hv⟩ := hs.f_surj u
    exact hu v hv
  have hsb : ∀ u v, g'.SameBlock (t.f u) (t.f v) ↔ T.SameBlock u v :=
    fun u v => (hblk _ _).trans (hs.sameBlock_iff u v)
  -- the components of `Γ_ω` are kept
  have hcarry : ((carryL Γ).map (Comp.map t.f)).Subperm g'.comps := by
    obtain ⟨l, hl, hsl⟩ := hB.carry
    have hlm : ∀ c ∈ l, c ∈ T.comps ∧ c.kind ≠ .dot := fun c hc =>
      ⟨hsl.subset hc, (mem_carryL (hl.subset hc)).2.2.1⟩
    have h1 : (l.map (Comp.map t.f)).Sublist t.g.comps := by
      rw [hs.comps_eq, ← filterMap_eq_map_of (step3_mergeComp T.step3_mrep t.f) _ l
        (fun c hc => hmc c (hlm c hc).1 (hlm c hc).2)]
      exact hsl.filterMap _
    have h2 : (l.map (Comp.map t.f)).Subperm
        (t.g.comps.filter fun d => !decide (d.kind = .dot)) := by
      have := h1.subperm.filter (fun d => !decide (d.kind = .dot))
      rwa [List.filter_eq_self.2 (fun d hd => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
        simp [Comp.map, (hlm c hc).2])] at this
    have h3 := (hfp.subperm_left.2 h2).trans (List.Sublist.subperm List.filter_sublist)
    exact (hl.map _).subperm_right.1 h3
  -- the clauses
  refine ⟨⟨?_, ?_, ?_, ?_, hXr, ?_, ?_⟩, ⟨hcarry, fun u v h => (hsb u v).2 (hB.blocks u v h)⟩,
    fun u hu => absurd hu (hnew u), Or.inr ?_, step3_final_oo1 hs hK hsub hfp,
    T, hH, Or.inr ⟨t, ht, g', hch, rfl⟩⟩
  · -- normal regular
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · have h1 : g'.comps.length ≤ t.g.comps.length := hsub.length_le
      have h2 : t.g.comps.length ≤ T.comps.length := by
        rw [hs.comps_eq]
        exact List.length_filterMap_le _ _
      have h3 : T.comps.length ≤ S := le_trans (by unfold sizeΦ; omega) hB.size
      change k + t.nOut + g'.comps.length ≤ C'
      omega
    · intro u v
      have h := hconn (hs.connNoX hB.conn) u v
      obtain ⟨w⟩ := h
      induction w with
      | nil => exact SimpleGraph.Reachable.refl _
      | cons hadj _ ih =>
        refine SimpleGraph.Reachable.trans ?_ ih
        rw [Graph.edgeGraphNoX, SimpleGraph.fromRel_adj] at hadj
        refine SimpleGraph.Adj.reachable ?_
        rw [Graph.edgeGraph, SimpleGraph.fromRel_adj]
        obtain ⟨hne, ⟨c, hc, -, h1, h2⟩ | ⟨c, hc, -, h1, h2⟩⟩ := hadj
        · exact ⟨hne, Or.inl ⟨c, hc, h1, h2⟩⟩
        · exact ⟨hne, Or.inr ⟨c, hc, h1, h2⟩⟩
    · intro a b
      rw [hwt]
      exact hs.internal hB.internal a b
    · intro c' hc' hk
      exact hs.noIntDot c' (hsub.subset hc') hk
    · intro c' hc' hk
      exact hs.solid_ne c' (hsub.subset hc') hk
    · intro u v _
      constructor
      · rintro ⟨c', hc', hk, hxy⟩
        obtain ⟨c, hc, rfl, -⟩ := hout c' hc'
        obtain ⟨d, hd, hdk, hdxy⟩ := hN2 c hc hk
        refine ⟨d.map t.f, hin d hd (by intro h; rw [h] at hdk; simp [Kind.isSolid] at hdk),
          hdk, ?_⟩
        simp only [Comp.map] at hxy ⊢
        rcases hdxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
      · rintro ⟨c', hc', hk, hxy⟩
        obtain ⟨c, hc, rfl, -⟩ := hout c' hc'
        obtain ⟨-, d, hd, hdk, hdxy⟩ := hB.solid c hc hk
        refine ⟨d.map t.f, hin d hd (by rw [hdk]; simp), hdk, ?_⟩
        simp only [Comp.map] at hxy ⊢
        rcases hdxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> tauto
  · -- order
    rw [hordg]
    have := hB.ord
    have : (0 : ℤ) ≤ ((d + 1 : ℕ) : ℤ) * (nWD T.comps : ℤ) := by positivity
    push_cast at *
    linarith
  · -- no `×`-dot inside a block
    intro c' hc' hk hb
    obtain ⟨c, hc, rfl, -⟩ := hout c' hc'
    exact hB.xapart c hc hk ((hsb _ _).1 hb)
  · -- dot excess
    change step3_eL g'.comps ≤ step3_eL Γ.comps
    rw [hge, hB.excess]
  · -- doubly connected
    intro hdcΓ
    exact Graph.Step3DCS.doublyConnected (hdc (Graph.Step3DCS.mergeT (hB.dc hdcΓ) ht).1)
  · -- chain of elementary steps
    exact (hB.chain.tail (QElemStep.merge T t ht)).trans (SelStep3Drop.chain hch)
  · -- output form
    by_cases hw : nWD T.comps = 0
    · left
      have hPl : g'.Plain := by
        intro c' hc'
        obtain ⟨h1, h2, h3, h4⟩ := hClean c' hc'
        refine ⟨h1, h2, ?_, h3, h4⟩
        intro ch dd hk
        obtain ⟨c, hc, rfl, -⟩ := hout c' hc'
        have : c ∈ T.comps.filter fun c => c.kind.step3_isWDB := by
          simp only [List.mem_filter]
          exact ⟨hc, by simp only [Comp.map] at hk; rw [hk]; rfl⟩
        unfold nWD at hw
        rw [List.length_eq_zero_iff] at hw
        rw [hw] at this
        simp at this
      refine ⟨hPl, ?_, ?_⟩
      · rw [hordg]
        rw [hw] at hordc
        push_cast at hordc
        linarith
      · rcases hcls with ⟨⟨e, he, hel, her, hem, hei, u, hu, hub⟩, -⟩ |
          ⟨hlf, ⟨e, he, hel, her, hem, hei, u, hu, hub⟩, -⟩
        · right
          have hek : e.kind ≠ .dot := by intro h; rw [h] at her; cases her
          refine ⟨⟨⟨e.map t.f, hin e he hek, by simp [Comp.map, hel]⟩, ?_⟩, ?_⟩
          · intro c' hc'
            obtain ⟨c, hc, rfl, -⟩ := hout c' hc'
            rcases hB.lab c hc with h | h
            · left; simp [Comp.map, h]
            · right; simp [Comp.map, h]
          · intro h
            have := h (e.map t.f) (hin e he hek) (by simp [Comp.map, hel])
              (by simpa [Comp.map] using her)
            have hb := (hsb u X).2 hub
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl
            · exact this.1 hb
            · exact this.2 hb
        · left
          have hek : e.kind ≠ .dot := by intro h; rw [h] at her; cases her
          refine ⟨?_, ?_⟩
          · intro c' hc'
            obtain ⟨c, hc, rfl, -⟩ := hout c' hc'
            simp [Comp.map, hlf c hc]
          · intro h
            have := h (e.map t.f) (hin e he hek) (by simp [Comp.map, hel])
              (by simpa [Comp.map] using her)
            have hb := (hsb u X).2 hub
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl
            · exact this.1 hb
            · exact this.2 hb
    · right
      refine ⟨?_, hClean⟩
      rw [hordg]
      have h2 : (1 : ℤ) ≤ nWD T.comps := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hw
      push_cast at hordc
      nlinarith

/-- The last step: the leading term is kept as it is, `O_merge` acts on the other graphs. -/
private theorem selStep3_final_out {d S C' : ℕ} {X : Atom k n} {Γ T : Graph k n} (hG : GIn Γ)
    (hB : Base d S X Γ T) (hK : OK1 Γ T)
    (hmin : ∀ c ∈ T.comps, c.minor = [])
    (hinv : ∀ c ∈ T.comps, c.kind.isInvB = false)
    (hN2 : ∀ c ∈ T.comps, c.kind = .xdot → HasS T.comps c.x c.y)
    (hcls : Cls d X Γ T) (hC : k + n + S ≤ C')
    (hH : Relation.ReflTransGen (SelStep3Step d X) Γ T) :
    DExp (SelOut3 C' d X Γ) 1 T (selStep3_final Γ.ord T) := by
  rcases hcls with h | h | h
  · exact selStep3_final_merge hB hK hmin hinv hN2 (Or.inl h) hC hH
  · exact selStep3_final_merge hB hK hmin hinv hN2 (Or.inr h) hC hH
  · exact selStep3_final_lead hG hB hK hmin hN2 h hC hH


open Classical in
/-- The phase of the `×`-dotted edges without solid edge, then the last step. -/
private theorem selStep3_clean_out {d S C' : ℕ} {X : Atom k n} {Γ : Graph k n} (hG : GIn Γ)
    (hC : k + n + S ≤ C') :
    ∀ (m : ℕ) (T : Graph k n), step3_nBad T.comps ≤ m → Base d S X Γ T → OK1 Γ T →
      (∀ c ∈ T.comps, c.minor = []) → (∀ c ∈ T.comps, c.kind.isInvB = false) →
      Cls d X Γ T → Relation.ReflTransGen (SelStep3Step d X) Γ T →
      DExp (SelOut3 C' d X Γ) (2 ^ m) T (selStep3_clean Γ.ord m T) := by
  have hfin : ∀ T : Graph k n, Base d S X Γ T → OK1 Γ T →
      (∀ c ∈ T.comps, c.minor = []) → (∀ c ∈ T.comps, c.kind.isInvB = false) →
      Cls d X Γ T → Relation.ReflTransGen (SelStep3Step d X) Γ T →
      (∀ c ∈ T.comps, step3_badB T.comps c = false) →
      DExp (SelOut3 C' d X Γ) 1 T (selStep3_final Γ.ord T) := by
    intro T hB hK hmin hinv hcls hH hnb
    refine selStep3_final_out hG hB hK hmin hinv ?_ hcls hC hH
    intro c hc hk
    by_contra hns
    have := hnb c hc
    simp only [step3_badB, hk, decide_true, Bool.true_and, Bool.not_eq_false'] at this
    rw [← solidJoinB_iff] at hns
    exact hns this
  intro m
  induction m with
  | zero =>
    intro T hm hB hK hmin hinv hcls hH
    simp only [selStep3_clean]
    refine (hfin T hB hK hmin hinv hcls hH fun c hc => ?_).mono (by simp)
    by_contra h
    have : c ∈ T.comps.filter (step3_badB T.comps) := List.mem_filter.2 ⟨hc, by simpa using h⟩
    have := List.length_pos_of_mem this
    unfold step3_nBad at hm
    omega
  | succ m ih =>
    intro T hm hB hK hmin hinv hcls hH
    rcases hf : T.comps.findIdx? (step3_badB T.comps) with _ | i
    · simp only [selStep3_clean, hf]
      exact (hfin T hB hK hmin hinv hcls hH (List.findIdx?_eq_none_iff.1 hf)).mono
        Nat.one_le_two_pow
    · obtain ⟨c, hc, hcb⟩ := selStep3_findIdx_some hf
      obtain ⟨hE, hv, -, hGs⟩ := selStep3_clean_step hG hB hK hmin hinv hcls hc hcb
      simp only [selStep3_clean, hf]
      rw [hE, selStep3_bind_self]
      have h2m : 2 ^ (m + 1) = [(⟨T.comps.eraseIdx i, T.coeff⟩ : Graph k n),
          ⟨T.comps.eraseIdx i ++ [mkC .dot c.x c.y], -T.coeff⟩].length * 2 ^ m := by
        simp [pow_succ, mul_comm]
      rw [h2m]
      refine DExp.bind _ (fun g => if g.XdotApart then selStep3_clean Γ.ord m g else []) hv
        fun g hg => ?_
      have hH' : Relation.ReflTransGen (SelStep3Step d X) Γ g :=
        hH.tail (.xdot i T g (by rw [hE]; exact List.mem_map_of_mem hg))
      obtain ⟨hlab, hgood⟩ := hGs g hg
      by_cases hxa : g.XdotApart
      · obtain ⟨hB', hK', hmin', hinv', hcls', hbad⟩ := hgood hxa
        simp only [hxa, ite_true]
        exact ih g (by omega) hB' hK' hmin' hinv' hcls' hH'
      · simp only [hxa, ite_false]
        exact DExp.nil _ (step1_valR_eq_zero g hlab hxa)

/-- The phase of [II, (4.21)], then the phase of the `×`-dotted edges without solid edge. -/
private theorem selStep3_taylor_out {d S C' : ℕ} {X : Atom k n} {Γ : Graph k n} (hG : GIn Γ)
    (hC : k + n + S ≤ C') :
    ∀ (m : ℕ) (T : Graph k n), step3_nInv T.comps ≤ m → Base d S X Γ T → OK1 Γ T →
      (∀ c ∈ T.comps, c.minor = []) → Cls d X Γ T →
      Relation.ReflTransGen (SelStep3Step d X) Γ T →
      DExp (SelOut3 C' d X Γ) ((d + 2) ^ m * 2 ^ S) T (selStep3_taylor Γ.ord d m T) := by
  have hcl : ∀ (m : ℕ) (T : Graph k n), Base d S X Γ T → OK1 Γ T →
      (∀ c ∈ T.comps, c.minor = []) → (∀ c ∈ T.comps, c.kind.isInvB = false) →
      Cls d X Γ T → Relation.ReflTransGen (SelStep3Step d X) Γ T →
      DExp (SelOut3 C' d X Γ) ((d + 2) ^ m * 2 ^ S) T
        (selStep3_clean Γ.ord (step3_nBad T.comps) T) := by
    intro m T hB hK hmin hinv hcls hH
    refine (selStep3_clean_out hG hC _ T le_rfl hB hK hmin hinv hcls hH).mono ?_
    calc 2 ^ step3_nBad T.comps ≤ 2 ^ S := Nat.pow_le_pow_right (by omega) (nBad_le_S hB)
      _ ≤ (d + 2) ^ m * 2 ^ S := Nat.le_mul_of_pos_left _ (by positivity)
  intro m
  induction m with
  | zero =>
    intro T hm hB hK hmin hcls hH
    have hinv : ∀ c ∈ T.comps, c.kind.isInvB = false := by
      intro c hc
      by_contra h
      have : c ∈ T.comps.filter fun c => c.kind.isInvB :=
        List.mem_filter.2 ⟨hc, by simpa using h⟩
      have := List.length_pos_of_mem this
      unfold step3_nInv at hm
      omega
    simp only [selStep3_taylor]
    exact hcl 0 T hB hK hmin hinv hcls hH
  | succ m ih =>
    intro T hm hB hK hmin hcls hH
    rcases hf : T.comps.findIdx? (fun c => c.kind.isInvB) with _ | i
    · simp only [selStep3_taylor, hf]
      exact hcl (m + 1) T hB hK hmin (List.findIdx?_eq_none_iff.1 hf) hcls hH
    · obtain ⟨c, hc, hci⟩ := selStep3_findIdx_some hf
      obtain ⟨Gs, hE, hlen, hv, hGs⟩ := selStep3_taylor_step hG hB hK hmin hcls hc hci
      simp only [selStep3_taylor, hf]
      rw [hE, selStep3_bind_self]
      have hpow : (d + 2) ^ (m + 1) * 2 ^ S = Gs.length * ((d + 2) ^ m * 2 ^ S) := by
        rw [hlen]; ring
      rw [hpow]
      refine DExp.bind Gs (fun g => selStep3_taylor Γ.ord d m g) hv fun g hg => ?_
      obtain ⟨hB', hK', hmin', hcls', hcnt⟩ := hGs g hg
      exact ih g (by omega) hB' hK' hmin' hcls'
        (hH.tail (.taylor i T g (by rw [hE]; exact List.mem_map_of_mem hg)))

/-- The phase of [II, (4.20)], then the phase of [II, (4.21)]. -/
private theorem selStep3_rev_out {d S C' : ℕ} {X : Atom k n} {Γ : Graph k n} (hG : GIn Γ)
    (hC : k + n + S ≤ C') :
    ∀ (m : ℕ) (T : Graph k n), step3_nMin T.comps ≤ m → Base d S X Γ T → OK1 Γ T →
      Cls d X Γ T → Relation.ReflTransGen (SelStep3Step d X) Γ T →
      DExp (SelOut3 C' d X Γ) (2 ^ m * ((d + 2) ^ S * 2 ^ S)) T
        (selStep3_rev Γ.ord d m X T) := by
  have hta : ∀ (m : ℕ) (T : Graph k n), Base d S X Γ T → OK1 Γ T →
      (∀ c ∈ T.comps, c.minor = []) → Cls d X Γ T →
      Relation.ReflTransGen (SelStep3Step d X) Γ T →
      DExp (SelOut3 C' d X Γ) (2 ^ m * ((d + 2) ^ S * 2 ^ S)) T
        (selStep3_taylor Γ.ord d (step3_nInv T.comps) T) := by
    intro m T hB hK hmin hcls hH
    have hinv : step3_nInv T.comps ≤ S :=
      le_trans (List.length_filter_le _ _) (le_trans (by unfold sizeΦ; omega) hB.size)
    refine (selStep3_taylor_out hG hC _ T le_rfl hB hK hmin hcls hH).mono ?_
    calc (d + 2) ^ step3_nInv T.comps * 2 ^ S ≤ (d + 2) ^ S * 2 ^ S :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hinv)
      _ ≤ 2 ^ m * ((d + 2) ^ S * 2 ^ S) := Nat.le_mul_of_pos_left _ (by positivity)
  intro m
  induction m with
  | zero =>
    intro T hm hB hK hcls hH
    have hmin : ∀ c ∈ T.comps, c.minor = [] := by
      intro c hc
      by_contra h
      have : c ∈ T.comps.filter fun c => !c.minor.isEmpty :=
        List.mem_filter.2 ⟨hc, by simpa [List.isEmpty_iff] using h⟩
      have := List.length_pos_of_mem this
      unfold step3_nMin at hm
      omega
    simp only [selStep3_rev]
    exact hta 0 T hB hK hmin hcls hH
  | succ m ih =>
    intro T hm hB hK hcls hH
    rcases hf : T.comps.findIdx? (fun c => !c.minor.isEmpty) with _ | i
    · have hmin : ∀ c ∈ T.comps, c.minor = [] := by
        intro c hc
        have := List.findIdx?_eq_none_iff.1 hf c hc
        simpa [List.isEmpty_iff] using this
      simp only [selStep3_rev, hf]
      exact hta (m + 1) T hB hK hmin hcls hH
    · obtain ⟨c, hc, hcm⟩ := selStep3_findIdx_some hf
      have hcT : c ∈ T.comps := List.mem_of_getElem? hc
      have hmX : c.minor = [X] := by
        rcases hB.minor c hcT with h | ⟨h, -⟩
        · rw [h] at hcm; simp at hcm
        · exact h
      obtain ⟨Gs, hE, hlen, hv, hGs⟩ := selStep3_rev_step hG hB hK hcls hc hmX
      simp only [selStep3_rev, hf]
      rw [hE, selStep3_bind_self]
      have hpow : 2 ^ (m + 1) * ((d + 2) ^ S * 2 ^ S) =
          Gs.length * (2 ^ m * ((d + 2) ^ S * 2 ^ S)) := by
        rw [hlen]; ring
      rw [hpow]
      refine DExp.bind Gs (fun g => selStep3_rev Γ.ord d m X g) hv fun g hg => ?_
      obtain ⟨⟨hB', hcls', hmin', -⟩, hK'⟩ := hGs g hg
      exact ih g (by omega) hB' hK' hcls'
        (hH.tail (SelStep3Step.of_revAt (by rw [hE]; exact List.mem_map_of_mem hg)))

/-- The removal of the label `P_X` when every labelled weight or edge has the minor `{X}`, then
the phase of [II, (4.20)]. -/
private theorem selStep3_dropP_out {d S C' : ℕ} {X : Atom k n} {Γ T : Graph k n} (hG : GIn Γ)
    (hC : k + n + S ≤ C') (hB : Base d S X Γ T) (hK : OK1 Γ T)
    (hnp : step3_nPend X T.comps = 0) (hcls : ClsP d X Γ T ∨ AllPendL X Γ T)
    (hH : Relation.ReflTransGen (SelStep3Step d X) Γ T) :
    DExp (SelOut3 C' d X Γ) (2 ^ S * ((d + 2) ^ S * 2 ^ S)) T (selStep3_dropP Γ.ord d X T) := by
  unfold selStep3_dropP
  by_cases hA : selStep3_AllMinor X T
  · rw [ite_eq_left hA]
    obtain ⟨-, hB', hK', hL, hv⟩ := (selStep3_dropP_step hB hK hnp hcls).1 hA
    have hst : SelStep3Step d X T T.dropLabels :=
      .dropP T ⟨hA.2, hB.lab⟩ fun c hc hl => by
        rw [hA.1 c hc hl ((hB.wf c hc).2 hl)]
        exact List.mem_singleton_self X
    have h := DExp.bind [T.dropLabels]
      (fun g => selStep3_rev Γ.ord d (step3_nMin g.comps) X g) hv fun g hg => by
        rw [List.mem_singleton.1 hg]
        exact (selStep3_rev_out hG hC _ _ le_rfl hB' hK' (Or.inr (Or.inr hL)) (hH.tail hst)).mono
          (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (nMin_le_S hB')))
    simpa using h
  · rw [ite_eq_right hA]
    exact (selStep3_rev_out hG hC _ _ le_rfl hB hK
      (Or.inl ((selStep3_dropP_step hB hK hnp hcls).2 hA)) hH).mono
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (nMin_le_S hB)))

/-- The phase of [II, (4.17)], then the removal of the label `P_X` and the phase of
[II, (4.20)]. -/
private theorem selStep3_schur_out {d S C' : ℕ} {X : Atom k n} {Γ : Graph k n} (hG : GIn Γ)
    (hC : k + n + S ≤ C') :
    ∀ (m : ℕ) (T : Graph k n), step3_nPend X T.comps ≤ m → Base d S X Γ T → OK1 Γ T →
      Step3PendInv X Γ T → (ClsP d X Γ T ∨ AllPendL X Γ T) →
      Relation.ReflTransGen (SelStep3Step d X) Γ T →
      DExp (SelOut3 C' d X Γ) (2 ^ m * (2 ^ S * ((d + 2) ^ S * 2 ^ S))) T
        (selStep3_schur Γ.ord d m X T) := by
  intro m
  induction m with
  | zero =>
    intro T hm hB hK hP hcls hH
    simp only [selStep3_schur]
    simpa using selStep3_dropP_out hG hC hB hK (by omega) hcls hH
  | succ m ih =>
    intro T hm hB hK hP hcls hH
    rcases hf : T.comps.findIdx? (step3_pendB X) with _ | i
    · have hnp : step3_nPend X T.comps = 0 := by
        unfold step3_nPend
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro c hc
        simp [List.findIdx?_eq_none_iff.1 hf c hc]
      simp only [selStep3_schur, hf]
      exact (selStep3_dropP_out hG hC hB hK hnp hcls hH).mono
        (Nat.le_mul_of_pos_left _ (by positivity))
    · obtain ⟨c, hc, hcp⟩ := selStep3_findIdx_some hf
      obtain ⟨Gs, hE, hlen, hv, hGs⟩ := selStep3_schur_step hG.plain hB hK hP hcls hc hcp
      simp only [selStep3_schur, hf]
      rw [hE, selStep3_bind_self]
      have hpow : 2 ^ (m + 1) * (2 ^ S * ((d + 2) ^ S * 2 ^ S)) =
          Gs.length * (2 ^ m * (2 ^ S * ((d + 2) ^ S * 2 ^ S))) := by
        rw [hlen]; ring
      rw [hpow]
      refine DExp.bind Gs (fun g => selStep3_schur Γ.ord d m X g) hv fun g hg => ?_
      obtain ⟨⟨hB', hP', hcls', hp'⟩, hK'⟩ := hGs g hg
      exact ih g (by omega) hB' hK' hP' hcls'
        (hH.tail (SelStep3Step.of_schurAt (by rw [hE]; exact List.mem_map_of_mem hg)))


open Classical in
/-- The splits of the atoms of `𝒢` against `X`, then the phase of [II, (4.17)]. -/
private theorem selStep3_split_out {d S C' : ℕ} {X : Atom k n} {Γ : Graph k n} (hG : GIn Γ)
    (hfree : Γ.LabelledFreeAtBlock X) (hC : k + n + S ≤ C') :
    ∀ (us : List (Atom k n)) (T : Graph k n),
      Base d S X Γ T → OK1 Γ T → sizeΦ d X T.comps + us.length ≤ S →
      step3_dg T.comps = step3_dg Γ.comps → (∀ g ∈ Γ.comps, g ∈ T.comps) →
      (∀ c ∈ T.comps, c.minor = []) → (∀ c ∈ T.comps, c.kind.isInvB = false) →
      AllPendL X Γ T →
      (∀ c ∈ T.comps, step3_pendB X c = true →
        c ∈ Γ.comps ∧ ∀ u ∈ [c.x, c.y], HasX T.comps u X ∨ u ∈ us) →
      (∀ u ∈ us, ∃ c ∈ Γ.comps, c.label.isSome = true ∧ c.kind.isRandom = true ∧
        u ∈ [c.x, c.y]) →
      Relation.ReflTransGen (SelStep3Step d X) Γ T →
      DExp (SelOut3 C' d X Γ) (2 ^ us.length * (2 ^ S * (2 ^ S * ((d + 2) ^ S * 2 ^ S)))) T
        (selStep3_split Γ.ord d X us T)
  | [], T, hB, hK, _, _, _, _, _, hA, hP, _, hH => by
    have hP' : Step3PendInv X Γ T := by
      intro c hc hp
      obtain ⟨h1, h2⟩ := hP c hc hp
      refine ⟨h1, ?_, ?_⟩
      · rcases h2 c.x (by simp) with h | h
        · exact h
        · simp at h
      · rcases h2 c.y (by simp) with h | h
        · exact h
        · simp at h
    simp only [selStep3_split]
    refine (selStep3_schur_out hG hC _ T le_rfl hB hK hP' (Or.inr hA) hH).mono ?_
    simp only [List.length_nil, pow_zero, one_mul]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (nPend_le_S hB))
  | u :: us, T, hB, hK, hsz, hdg, hsub, hmin, hinv, hA, hP, hus, hH => by
    obtain ⟨c₀, hc₀, hl₀, hr₀, hu₀⟩ := hus u (List.mem_cons_self ..)
    have hpow' : 2 ^ us.length * (2 ^ S * (2 ^ S * ((d + 2) ^ S * 2 ^ S))) ≤
        2 ^ (u :: us).length * (2 ^ S * (2 ^ S * ((d + 2) ^ S * 2 ^ S))) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by simp))
    by_cases hux : HasX T.comps u X
    · -- `u` is already `×`-dotted to `X`
      simp only [selStep3_split, ite_eq_left hux]
      refine (selStep3_split_out hG hfree hC us T hB hK ?_ hdg hsub hmin hinv hA ?_
        (fun v hv => hus v (List.mem_cons_of_mem _ hv)) hH).mono hpow'
      · simp only [List.length_cons] at hsz
        omega
      · intro c hc hp
        obtain ⟨h1, h2⟩ := hP c hc hp
        refine ⟨h1, fun v hv => ?_⟩
        rcases h2 v hv with h | h
        · exact Or.inl h
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inl hux
          · exact Or.inr h
    have hBsz : sizeΦ d X T.comps + 1 ≤ S := by
      simp only [List.length_cons] at hsz
      omega
    obtain ⟨hE, hv, hlab₁, hgood₁, hB₂, hK₂, hdg₂⟩ :=
      selStep3_split_step hG hfree hB hK hBsz hdg hsub hc₀ hl₀ hr₀ hu₀
    have hst : ∀ g ∈ [(⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n),
        ⟨T.comps ++ [mkC .xdot u X], T.coeff⟩], SelStep3Step d X T g := fun g hg =>
      .split u T g (by rw [hE]; exact List.mem_map_of_mem hg)
    set B' := 2 ^ S * (2 ^ S * ((d + 2) ^ S * 2 ^ S)) with hB'def
    have hX : ∀ v w, HasX T.comps v w → HasX (T.comps ++ [mkC .xdot u X]) v w :=
      fun v w h => hasX_mono (fun d hd => List.mem_append_left _ hd) h
    -- `u` is joined to `X` by no solid edge of `Γ`
    have hnS : ¬ HasS Γ.comps u X := by
      rintro ⟨g, hg, hgk, hgxy⟩
      obtain ⟨d, hd, hdk, hdxy⟩ := hG.sx g hg hgk
      apply hux
      refine ⟨d, hsub d hd, hdk, ?_⟩
      rcases hgxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hdxy with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact Or.inl ⟨h3.trans h1, h4.trans h2⟩
      · exact Or.inr ⟨h3.trans h2, h4.trans h1⟩
      · exact Or.inr ⟨h3.trans h1, h4.trans h2⟩
      · exact Or.inl ⟨h3.trans h2, h4.trans h1⟩
    -- the term with `u ≠ X`
    have h₂ := selStep3_split_out hG hfree hC us _ hB₂ hK₂ ?_ hdg₂ ?_ ?_ ?_ ?_ ?_
      (fun v hv => hus v (List.mem_cons_of_mem _ hv)) (hH.tail (hst _ (by simp)))
    · simp only [selStep3_split, ite_eq_right hux]
      refine (DExp.append (B₁ := B') hv ?_ h₂).mono ?_
      · -- the term with `u` identified with `X`
        by_cases hxa : (⟨T.comps ++ [mkC .dot u X], T.coeff⟩ : Graph k n).XdotApart
        · rw [ite_eq_left hxa]
          obtain ⟨hB₁, hK₁, hcls⟩ := hgood₁ hxa
          refine (selStep3_clean_out hG hC _ _ le_rfl hB₁ hK₁ ?_ ?_ (Or.inl hcls)
            (hH.tail (hst _ (by simp)))).mono ?_
          · intro d hd
            rcases List.mem_append.1 hd with h | h
            · exact hmin d h
            · rw [List.mem_singleton.1 h]; rfl
          · intro d hd
            rcases List.mem_append.1 hd with h | h
            · exact hinv d h
            · rw [List.mem_singleton.1 h]; rfl
          · calc 2 ^ step3_nBad (T.comps ++ [mkC .dot u X]) ≤ 2 ^ S :=
                Nat.pow_le_pow_right (by omega) (nBad_le_S hB₁)
              _ ≤ B' := by
                rw [hB'def]
                exact Nat.le_mul_of_pos_right _ (by positivity)
        · rw [ite_eq_right hxa]
          exact DExp.nil _ (step1_valR_eq_zero _ hlab₁ hxa)
      · have := Nat.one_le_two_pow (n := us.length)
        rw [List.length_cons, pow_succ]
        nlinarith
    · rw [sizeΦ_append_xdot _ (Or.inr rfl)]
      simp only [List.length_cons] at hsz
      omega
    · exact fun g hg => List.mem_append_left _ (hsub g hg)
    · intro d hd
      rcases List.mem_append.1 hd with h | h
      · exact hmin d h
      · rw [List.mem_singleton.1 h]; rfl
    · intro d hd
      rcases List.mem_append.1 hd with h | h
      · exact hinv d h
      · rw [List.mem_singleton.1 h]; rfl
    · obtain ⟨hA1, ⟨w, hw, hwl⟩, us', hus', hp⟩ := hA
      refine ⟨?_, ⟨w, List.mem_append_left _ hw, hwl⟩, us' ++ [u], ?_, ?_⟩
      · intro d hd hdl hdr
        rcases List.mem_append.1 hd with h | h
        · exact hA1 d h hdl hdr
        · rw [List.mem_singleton.1 h] at hdr; simp [mkC, Kind.isRandom] at hdr
      · intro v hv
        rcases List.mem_append.1 hv with h | h
        · exact hus' v h
        · rw [List.mem_singleton.1 h]
          exact ⟨hnS, c₀, hc₀, hr₀, hu₀⟩
      · rw [List.map_append, List.map_append, List.map_singleton, List.map_singleton,
          ← List.append_assoc]
        exact hp.append_right _
    · intro d hd hdp
      rcases List.mem_append.1 hd with h | h
      · obtain ⟨h1, h2⟩ := hP d h hdp
        refine ⟨h1, fun v hv => ?_⟩
        rcases h2 v hv with h3 | h3
        · exact Or.inl (hX _ _ h3)
        · rcases List.mem_cons.1 h3 with rfl | h4
          · exact Or.inl ⟨mkC .xdot v X, by simp, rfl, Or.inl ⟨rfl, rfl⟩⟩
          · exact Or.inr h4
      · rw [List.mem_singleton.1 h] at hdp; simp [step3_pendB, mkC] at hdp

end SelStep3Phases


/-! ## The clauses of [II, Lemma 4.14] for the run -/

section SelStep3Main

/-- **[II, Lemma 4.14]** for the run `selStep3`, without an error order: for all `k`, `C`, `e`
there are `K`, `C'` such that, under the hypotheses of `selStep3_clauses'`, the run has at most `K`
terms and the value of `Γ`, and every output graph `t` has the clauses `Tracked.QBase C'` and
`Tracked.Carries`, its new atoms are joined to the image of `x` by waved edges, and it keeps the
components at the external atoms, has one of the three forms of `selStep3_clauses'` and the
history `SelStep3Hist`. No bound on the scaling order of `Γ` is assumed. -/
theorem selStep3_clauses' (k C e : ℕ) :
    ∃ K C' : ℕ, ∀ (n₀ : ℕ) (x₀ : Fin n₀) (Γ : Graph k n₀) (d : ℕ), d ≤ e →
      Γ.Normal C → Γ.IsPFormAt (.inr x₀) → Γ.Plain → Γ.LabelledFreeAtBlock (.inr x₀) →
      (selStep3 d (.inr x₀) Γ).length ≤ K ∧ (selStep3 d (.inr x₀) Γ).ValueEq Γ modelAdm ∧
      ∀ t ∈ selStep3 d (.inr x₀) Γ,
        (t.QBase C' (.inr x₀) Γ ∧ t.Carries Γ ∧
          ∀ u, t.IsNew u → t.g.wavedGraph.Reachable (t.f (.inr x₀)) u) ∧ Step3OO1 Γ t ∧
        ((∃ T : Graph k n₀, t = Tracked.self T ∧ T.comps.Perm Γ.dropLabels.comps ∧
            T.Plain ∧ T.LabelFree) ∨
          (t.g.Plain ∧ Γ.paperOrd + 1 ≤ t.g.paperOrd ∧
            ((t.g.LabelFree ∧ ¬ t.g.UnlabelledFreeAtBlock (t.f (.inr x₀))) ∨
              (t.g.IsPFormAt (t.f (.inr x₀)) ∧ ¬ t.g.LabelledFreeAtBlock (t.f (.inr x₀))))) ∨
          (t.g.Clean ∧ Γ.paperOrd + d + 1 ≤ t.g.paperOrd)) ∧
        SelStep3Hist d (.inr x₀) Γ t := by
  set S := (e + 6) * C + 1 with hSdef
  refine ⟨2 ^ (2 * C) * (2 ^ S * (2 ^ S * ((e + 2) ^ S * 2 ^ S))), C + S, ?_⟩
  intro n₀ x Γ d hde hN hPF hP hfree
  set X : Atom k n₀ := .inr x with hXdef
  suffices h : DExp (SelOut3 (C + S) d X Γ)
      (2 ^ (2 * C) * (2 ^ S * (2 ^ S * ((e + 2) ^ S * 2 ^ S)))) Γ (selStep3 d X Γ) by
    obtain ⟨hv, hlen, hall⟩ := h
    refine ⟨hlen, hv, fun t ht => ?_⟩
    obtain ⟨hbase, hcar, hnew, hform, hoo, hhist⟩ := hall t ht
    have hex : t.g.dotExcess ≤ Γ.dotExcess := hbase.2.2.2.1
    refine ⟨⟨hbase, hcar, hnew⟩, hoo, ?_, hhist⟩
    · rcases hform with ⟨T, rfl, hp⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
      · refine Or.inl ⟨T, rfl, hp, fun c hc => ?_, fun c hc => ?_⟩
        · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 (hp.subset hc)
          obtain ⟨h1, h2, h3, h4, h5⟩ := hP c₀ hc₀
          exact ⟨h1, h2, h3, h4, h5.1, fun h => by simp at h⟩
        · obtain ⟨c₀, -, rfl⟩ := List.mem_map.1 (hp.subset hc)
          rfl
      · refine Or.inr (Or.inl ⟨h1, ?_, h3⟩)
        unfold Graph.paperOrd
        linarith
      · refine Or.inr (Or.inr ⟨h2, ?_⟩)
        unfold Graph.paperOrd
        linarith
  have hdotlab : ∀ d ∈ Γ.comps, (d.kind = .dot ∨ d.kind = .xdot) → d.label = none :=
    dotlab_of_wf fun c hc => (hP c hc).2.2.2.2
  have hsize := hN.1.size
  have hC : k + n₀ + S ≤ C + S := by omega
  -- a graph with a `×`-dotted edge inside a block has value `0`
  by_cases hxa : Γ.XdotApart
  swap
  · rw [selStep3, ite_eq_right hxa]
    exact DExp.nil _ (step1_valR_eq_zero Γ hdotlab hxa)
  -- the facts on the input
  have hG : GIn Γ := by
    refine ⟨hP, ?_, ?_, hN.1.noIntDot⟩
    · intro g hg hk
      have hne : g.x ≠ g.y := fun h => hxa g hg hk (by rw [h]; exact SimpleGraph.Reachable.refl _)
      exact (hN.2.2 _ _ hne).1 ⟨g, hg, hk, Or.inl ⟨rfl, rfl⟩⟩
    · intro g hg hk
      have hne := hN.2.1 g hg hk
      exact (hN.2.2 _ _ hne).2 ⟨g, hg, hk, Or.inl ⟨rfl, rfl⟩⟩
  -- the size bound at the input
  have hlenΓ : Γ.comps.length ≤ C := by omega
  have hpendΓ : step3_nPend X Γ.comps ≤ C := le_trans (List.length_filter_le _ _) hlenΓ
  have hminΓ : step3_nMin Γ.comps = 0 := by
    unfold step3_nMin
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    simp [(hP c hc).1]
  have hinvΓ : step3_nInv Γ.comps = 0 := by
    unfold step3_nInv
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    have := (hP c hc).2.1
    revert this
    cases c.kind <;> simp [Kind.isInvB]
  have hΦ : sizeΦ d X Γ.comps ≤ (e + 4) * C := by
    unfold sizeΦ
    rw [hminΓ, hinvΓ]
    have h1 : (d + 3) * (step3_nPend X Γ.comps + 0) ≤ (e + 3) * C :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  -- the atoms of the labelled factors
  rw [selStep3, ite_eq_left hxa]
  set R := Γ.comps.filter fun c => c.label.isSome && c.kind.isRandom with hR
  have hus : selStep3_us Γ = R.flatMap fun c => [c.x, c.y] := rfl
  have hlenus : (selStep3_us Γ).length ≤ 2 * C := by
    have h1 : (selStep3_us Γ).length = 2 * R.length := by
      rw [hus, List.length_flatMap]
      simp only [List.length_cons, List.length_nil]
      induction R with
      | nil => simp
      | cons a l ih => simp; ring
    have h2 : R.length ≤ C := le_trans (List.length_filter_le _ _) hlenΓ
    omega
  have hB := step3_base_init (D' := d) (S := S) hN hPF hP hxa rfl
    (by have : (e + 4) * C ≤ S := by rw [hSdef]; nlinarith
        omega)
  have hE := selStep3_split_out hG hfree hC (selStep3_us Γ) Γ hB (OK1.refl Γ)
    (by have : (e + 4) * C + 2 * C ≤ S := by rw [hSdef]; nlinarith
        omega) rfl (fun g hg => hg)
    (fun c hc => (hP c hc).1)
    (fun c hc => by have := (hP c hc).2.1; revert this; cases c.kind <;> simp [Kind.isInvB])
    ?_ ?_ ?_ Relation.ReflTransGen.refl
  · refine hE.mono (Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hlenus) ?_)
    refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ?_))
    exact Nat.pow_le_pow_left (by omega) S
  · refine ⟨?_, hPF.1, [], by simp, by simp⟩
    intro c hc hl hr
    left
    have hcx := (hfree c hc hl hr).1
    have hcy := (hfree c hc hl hr).2
    have hx : c.x ≠ X := fun h => hcx (by rw [h]; exact SimpleGraph.Reachable.refl _)
    have hy : c.y ≠ X := fun h => hcy (by rw [h]; exact SimpleGraph.Reachable.refl _)
    simp [step3_pendB, hl, hr, (hP c hc).1, hx, hy]
  · intro c hc hp
    refine ⟨hc, fun u hu => Or.inr ?_⟩
    rw [hus, List.mem_flatMap]
    refine ⟨c, ?_, hu⟩
    rw [hR, List.mem_filter]
    simp only [step3_pendB, Bool.and_eq_true] at hp
    exact ⟨hc, by simp only [Bool.and_eq_true]; exact ⟨hp.1.1.1.1, hp.1.1.1.2⟩⟩
  · intro u hu
    rw [hus, List.mem_flatMap] at hu
    obtain ⟨c, hcR, hu⟩ := hu
    rw [hR, List.mem_filter] at hcR
    simp only [Bool.and_eq_true] at hcR
    exact ⟨c, hcR.1, hcR.2.1, hcR.2.2, hu⟩

end SelStep3Main


section SelStep3Instances

end SelStep3Instances

end RBM8D.Graphs
