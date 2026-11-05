import RBM8D.Graph.Local.IBP
import RBM8D.Graph.Local.Dot

/-!
# Edge expansions

`O_multi-e`, `O_GG`, `O_GḠ` ([I, Defs 3.11, 3.15, 3.18] = [II, Defs 4.4–4.6]) and their value preservation.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-- The indices of the solid edges of charge `ch` leaving `x` (`out = true`) or entering `x`
(`out = false`); solid self-loops are not counted. -/
def Graph.edgeIdx {k n : ℕ} (Γ : Graph k n) (x : Atom k n) (ch : Charge) (out : Bool) : List ℕ :=
  (Γ.comps.zipIdx.filter fun p => p.1.kind == .G ch &&
    (if out then p.1.x == x && p.1.y != x else p.1.y == x && p.1.x != x)).map Prod.snd

/-- `u` and `v` are joined by a `×`-dotted edge. -/
def Graph.hasXdot {k n : ℕ} (Γ : Graph k n) (u v : Atom k n) : Bool :=
  Γ.comps.any fun c => c.kind == .xdot && ((c.x == u && c.y == v) || (c.x == v && c.y == u))

/-- Every solid edge at the indices `is` joins `x` to an atom joined to `x` by a `×`-dotted
edge. -/
def Graph.xdotsAt {k n : ℕ} (Γ : Graph k n) (x : Atom k n) (is : List ℕ) : Bool :=
  is.all fun j =>
    match Γ.comps[j]? with
    | some c => Γ.hasXdot x (if c.x == x then c.y else c.x)
    | none => false

/-- The components at the indices `is`. -/
def pickIdxs {α : Type*} (is : List ℕ) (l : List α) : List α :=
  (l.zipIdx.filter fun p => is.contains p.2).map Prod.fst

/-- The multi-edge expansion [I, (3.13)] at `x` of `𝒢 = ∏ G_{x y_i} ∏ Ḡ_{x y'_i} ∏ G_{w_i x}
∏ Ḡ_{w'_i x} f(G)` with `k₁ ≥ 1` (case (i) of [I, Def 3.11]); `G_{x y₁}` is the first edge of
charge `plus` leaving `x`, and the `×`-dotted edges between `x` and the other ends of its solid
edges are required (`none` otherwise). The
new atom is `α`; the terms are, in order: the two families of main terms, the light weight
terms, `m ∑_α s_{xα}(G_{αα} - m) 𝒢`, the `(k₁ - 1)` and `k₄` terms, the derivative terms of `f`,
and `𝒬_multi-e`. -/
def multiEOut {k n : ℕ} (x : Atom k n) (Γ : Graph k n) : Option (TExpansion k n) :=
  match Γ.edgeIdx x .plus true with
  | [] => none
  | i₁ :: is₂ =>
    match Γ.comps[i₁]? with
    | none => none
    | some e₁ =>
      let jsM := Γ.edgeIdx x .minus true
      let jsP := Γ.edgeIdx x .plus false
      let k₄ := (Γ.edgeIdx x .minus false).length
      let xIdx := Γ.edgeIdx x .plus true ++ jsM ++ jsP ++ Γ.edgeIdx x .minus false
      if !Γ.xdotsAt x xIdx then none else
      let c := Γ.coeff
      let x₁ : Atom k (n + 1) := liftA 1 x
      let a₁ : Atom k (n + 1) := newA 0
      let y₁ : Atom k (n + 1) := liftA 1 e₁.y
      let rest := liftCs 1 (Γ.comps.eraseIdx i₁)
      let fL := liftCs 1 (eraseIdxs xIdx Γ.comps)
      let xe := liftCs 1 (pickIdxs (xIdx.filter (· != i₁)) Γ.comps)
      let sx : Comp (Atom k (n + 1)) := mkC (.waved .s) x₁ a₁
      let t₁ (cs : List (Comp (Atom k (n + 1)))) (d : Coeff) : Tracked k n :=
        ⟨n + 1, ⟨cs, d⟩, liftA 1⟩
      let baseM (j : ℕ) : List (Comp (Atom k (n + 1))) :=
        liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
          [sx, mkC (.G .plus) a₁ y₁, mkC (.G .minus) a₁ (liftA 1 ((Γ.comps.getD j e₁).y))]
      let baseP (j : ℕ) : List (Comp (Atom k (n + 1))) :=
        liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
          [sx, mkC (.G .plus) a₁ y₁, mkC (.G .plus) (liftA 1 ((Γ.comps.getD j e₁).x)) a₁]
      let e1 := rest ++ [sx, mkC (.G .plus) x₁ a₁, mkC (.G .plus) a₁ y₁]
      let e2 := rest ++ [sx, mkC (.G .minus) a₁ x₁, mkC (.G .plus) a₁ y₁]
      let l3 := liftCs 1 Γ.comps ++ [sx, mkC (.light .plus) a₁ a₁]
      let ds := (dTerms a₁ x₁ fL).map fun d => xe ++ d ++ [sx, mkC (.G .plus) a₁ y₁]
      some <|
        jsM.map (fun j => t₁ (baseM j) (cm * cmb * c)) ++
        jsP.map (fun j => t₁ (baseP j) (cm * cm * c)) ++
        jsM.map (fun j => t₁ (baseM j ++ [mkC (.light .minus) x₁ x₁]) (cm * c)) ++
        jsP.map (fun j => t₁ (baseP j ++ [mkC (.light .plus) x₁ x₁]) (cm * c)) ++
        [t₁ l3 (cm * c)] ++
        (if is₂.isEmpty then [] else [t₁ e1 ((is₂.length : Coeff) * cm * c)]) ++
        (if k₄ = 0 then [] else [t₁ e2 ((k₄ : Coeff) * cm * c)]) ++
        ds.map (fun d => t₁ d (cm * c)) ++
        [⟨n, ⟨labelQs x Γ.comps, c⟩, id⟩] ++
        jsM.map (fun j => t₁ (labelQs x₁ (baseM j ++ [mkC (.weight .minus) x₁ x₁])) (-cm * c)) ++
        jsP.map (fun j => t₁ (labelQs x₁ (baseP j ++ [mkC (.weight .plus) x₁ x₁])) (-cm * c)) ++
        [t₁ (labelQs x₁ l3) (-cm * c)] ++
        (if is₂.isEmpty then [] else [t₁ (labelQs x₁ e1) (-(is₂.length : Coeff) * cm * c)]) ++
        (if k₄ = 0 then [] else [t₁ (labelQs x₁ e2) (-(k₄ : Coeff) * cm * c)]) ++
        ds.map (fun d => t₁ (labelQs x₁ d) (-cm * c))

/-- The multi-edge expansion [I, (3.14)] at `x` of `𝒢` with `k₁ = k₂ = 0`, `k₃ ≥ 1` (case (iii)
of [I, Def 3.11]); `G_{w₁ x}` is the first edge of charge `plus` entering `x`, and the
`×`-dotted edges between `x` and the other ends of its solid edges are required (`none`
otherwise). The terms are, in order: the main
terms, the light weight terms, `m ∑_α s_{xα}(G_{αα} - m) 𝒢`, the `(k₃ - 1)` term, the derivative
terms `-m ∑_α s_{xα} (𝒢/(G_{w₁x} f)) G_{w₁α} ∂_{h_{xα}} f`, and `𝒬_multi-e`. -/
def multiEIn {k n : ℕ} (x : Atom k n) (Γ : Graph k n) : Option (TExpansion k n) :=
  match Γ.edgeIdx x .plus false with
  | [] => none
  | i₁ :: is₂ =>
    match Γ.comps[i₁]? with
    | none => none
    | some e₁ =>
      let jsM := Γ.edgeIdx x .minus false
      let xIdx := Γ.edgeIdx x .plus false ++ jsM
      if !Γ.xdotsAt x xIdx then none else
      let c := Γ.coeff
      let x₁ : Atom k (n + 1) := liftA 1 x
      let a₁ : Atom k (n + 1) := newA 0
      let w₁ : Atom k (n + 1) := liftA 1 e₁.x
      let rest := liftCs 1 (Γ.comps.eraseIdx i₁)
      let fL := liftCs 1 (eraseIdxs xIdx Γ.comps)
      let xe := liftCs 1 (pickIdxs (xIdx.filter (· != i₁)) Γ.comps)
      let sx : Comp (Atom k (n + 1)) := mkC (.waved .s) x₁ a₁
      let t₁ (cs : List (Comp (Atom k (n + 1)))) (d : Coeff) : Tracked k n :=
        ⟨n + 1, ⟨cs, d⟩, liftA 1⟩
      let baseM (j : ℕ) : List (Comp (Atom k (n + 1))) :=
        liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
          [sx, mkC (.G .plus) w₁ a₁, mkC (.G .minus) (liftA 1 ((Γ.comps.getD j e₁).x)) a₁]
      let e1 := rest ++ [sx, mkC (.G .plus) w₁ a₁, mkC (.G .plus) a₁ x₁]
      let l3 := liftCs 1 Γ.comps ++ [sx, mkC (.light .plus) a₁ a₁]
      let ds := (dTerms x₁ a₁ fL).map fun d => xe ++ d ++ [sx, mkC (.G .plus) w₁ a₁]
      some <|
        jsM.map (fun j => t₁ (baseM j) (cm * cmb * c)) ++
        jsM.map (fun j => t₁ (baseM j ++ [mkC (.light .minus) x₁ x₁]) (cm * c)) ++
        [t₁ l3 (cm * c)] ++
        (if is₂.isEmpty then [] else [t₁ e1 ((is₂.length : Coeff) * cm * c)]) ++
        ds.map (fun d => t₁ d (cm * c)) ++
        [⟨n, ⟨labelQs x Γ.comps, c⟩, id⟩] ++
        jsM.map (fun j => t₁ (labelQs x₁ (baseM j ++ [mkC (.weight .minus) x₁ x₁])) (-cm * c)) ++
        [t₁ (labelQs x₁ l3) (-cm * c)] ++
        (if is₂.isEmpty then [] else [t₁ (labelQs x₁ e1) (-(is₂.length : Coeff) * cm * c)]) ++
        ds.map (fun d => t₁ (labelQs x₁ d) (-cm * c))

/-- The operator `Ô^{(x)}_multi-e` of [I, Def 3.11]: case (i) if an edge of charge `plus` leaves
`x`; case (ii) (complex conjugation of case (i)) if only edges of charge `minus` leave `x`;
case (iii) if no edge leaves `x` and an edge of charge `plus` enters `x`; case (iv) (complex
conjugation of case (iii)) otherwise. `none` if no solid edge is attached to `x` or a required
`×`-dotted edge is missing. -/
def multiEHat {k n : ℕ} (x : Atom k n) (Γ : Graph k n) : Option (TExpansion k n) :=
  if !(Γ.edgeIdx x .plus true).isEmpty then multiEOut x Γ
  else if !(Γ.edgeIdx x .minus true).isEmpty then (multiEOut x Γ.conj).map TExpansion.conj
  else if !(Γ.edgeIdx x .plus false).isEmpty then multiEIn x Γ
  else if !(Γ.edgeIdx x .minus false).isEmpty then (multiEIn x Γ.conj).map TExpansion.conj
  else none

/-- The multi-edge expansion `O^{(x)}_multi-e = O_dot ∘ Ô^{(x)}_multi-e` of [I, Def 3.11] =
[II, Def 4.4], tracked; the identity if no solid edge is attached to `x`, if a required
`×`-dotted edge is missing, or on graphs with a `P`/`Q` label, a `G^{(T)}` entry or a
`(G_{xx})⁻¹` or `W_D` weight. -/
def oMultiET {k n : ℕ} (x : Atom k n) (Γ : Graph k n) : TExpansion k n :=
  if !(Γ.comps.all Comp.isPlainB) then [Tracked.self Γ] else
  match multiEHat x Γ with
  | some E => E.bind fun _ g => oDotT g
  | none => [Tracked.self Γ]

/-- The multi-edge expansion `O^{(x)}_multi-e` ([I, Def 3.11] = [II, Def 4.4]). -/
def oMultiE {k n : ℕ} (x : Atom k n) (Γ : Graph k n) : Expansion k := (oMultiET x Γ).forget

/-- The `GG` expansion [I, (3.17)] at `x` of `𝒢 = G_{xy} G_{y'x} f(G)`, where `G_{xy}`,
`G_{y'x}` are the only solid edges attached to `x`, both of charge `plus`; the `×`-dotted edges
`x ≠ y`, `x ≠ y'` are required (`none` otherwise). The new atoms are `α` (and `β`); the terms
are, in order:
`m S⁺_{xy} G_{y'y} f`, the four light weight terms, the two derivative families, and the nine
families of `𝒬_GG`. -/
def ggPos {k n : ℕ} (x : Atom k n) (Γ : Graph k n) : Option (TExpansion k n) :=
  if Γ.deg x != 2 then none else
  match Γ.edgeIdx x .plus true, Γ.edgeIdx x .plus false with
  | [i], [j] =>
    match Γ.comps[i]?, Γ.comps[j]? with
    | some e, some e' =>
      if !Γ.xdotsAt x [i, j] then none else
      let c := Γ.coeff
      let y := e.y
      let y' := e'.x
      let f := eraseIdxs [i, j] Γ.comps
      let x₁ : Atom k (n + 1) := liftA 1 x
      let x₂ : Atom k (n + 2) := liftA 2 x
      let a₁ : Atom k (n + 1) := newA 0
      let a₂ : Atom k (n + 2) := newA 0
      let b₂ : Atom k (n + 2) := newA 1
      let y₁ : Atom k (n + 1) := liftA 1 y
      let y'₁ : Atom k (n + 1) := liftA 1 y'
      let y₂ : Atom k (n + 2) := liftA 2 y
      let y'₂ : Atom k (n + 2) := liftA 2 y'
      let F₁ := liftCs 1 f
      let F₂ := liftCs 2 f
      let t₁ (cs : List (Comp (Atom k (n + 1)))) (d : Coeff) : Tracked k n :=
        ⟨n + 1, ⟨cs, d⟩, liftA 1⟩
      let t₂ (cs : List (Comp (Atom k (n + 2)))) (d : Coeff) : Tracked k n :=
        ⟨n + 2, ⟨cs, d⟩, liftA 2⟩
      let main := f ++ [solidC .plus y' y]
      let d₁ := (dTerms a₁ x₁ F₁).map fun d =>
        d ++ [mkC (.G .plus) a₁ y₁, mkC (.G .plus) y'₁ x₁]
      let d₂ := (dTerms b₂ a₂ F₂).map fun d =>
        d ++ [mkC (.G .plus) b₂ y₂, mkC (.G .plus) y'₂ a₂]
      some <|
        [⟨n, ⟨main ++ [mkC (.waved .plus) x y], cm * c⟩, id⟩,
          t₁ (liftCs 1 Γ.comps ++ [mkC (.waved .s) x₁ a₁, mkC (.light .plus) a₁ a₁]) (cm * c),
          t₂ (F₂ ++ [mkC (.waved .plus) x₂ a₂, mkC (.waved .s) a₂ b₂, mkC (.light .plus) b₂ b₂,
            mkC (.G .plus) a₂ y₂, mkC (.G .plus) y'₂ a₂]) (cm * c),
          t₁ (F₁ ++ [mkC (.light .plus) x₁ x₁, mkC (.waved .s) x₁ a₁, mkC (.G .plus) a₁ y₁,
            mkC (.G .plus) y'₁ a₁]) (cm * c),
          t₂ (F₂ ++ [mkC (.waved .plus) x₂ a₂, mkC (.waved .s) a₂ b₂, mkC (.light .plus) a₂ a₂,
            mkC (.G .plus) b₂ y₂, mkC (.G .plus) y'₂ b₂]) (cm * c)] ++
        d₁.map (fun d => t₁ (d ++ [mkC (.waved .s) x₁ a₁]) (cm * c)) ++
        d₂.map (fun d => t₂ (d ++ [mkC (.waved .plus) x₂ a₂, mkC (.waved .s) a₂ b₂]) (cm * c)) ++
        [⟨n, ⟨labelQs x Γ.comps, c⟩, id⟩,
          t₁ (labelQs a₁ (F₁ ++ [mkC (.G .plus) a₁ y₁, mkC (.G .plus) y'₁ a₁]) ++
            [mkC (.waved .plus) x₁ a₁]) c,
          ⟨n, ⟨labelQs y main ++ [mkC (.waved .plus) x y], -cm * c⟩, id⟩,
          t₁ (labelQs x₁ (liftCs 1 Γ.comps ++ [mkC (.light .plus) a₁ a₁]) ++
            [mkC (.waved .s) x₁ a₁]) (-cm * c),
          t₂ (labelQs a₂ (F₂ ++ [mkC (.light .plus) b₂ b₂, mkC (.G .plus) a₂ y₂,
            mkC (.G .plus) y'₂ a₂]) ++ [mkC (.waved .plus) x₂ a₂, mkC (.waved .s) a₂ b₂]) (-cm * c),
          t₁ (labelQs x₁ (F₁ ++ [mkC (.weight .plus) x₁ x₁, mkC (.G .plus) a₁ y₁,
            mkC (.G .plus) y'₁ a₁]) ++ [mkC (.waved .s) x₁ a₁]) (-cm * c),
          t₂ (labelQs a₂ (F₂ ++ [mkC (.weight .plus) a₂ a₂, mkC (.G .plus) b₂ y₂,
            mkC (.G .plus) y'₂ b₂]) ++ [mkC (.waved .plus) x₂ a₂, mkC (.waved .s) a₂ b₂])
            (-cm * c)] ++
        d₁.map (fun d => t₁ (labelQs x₁ d ++ [mkC (.waved .s) x₁ a₁]) (-cm * c)) ++
        d₂.map (fun d => t₂ (labelQs a₂ d ++ [mkC (.waved .plus) x₂ a₂, mkC (.waved .s) a₂ b₂])
          (-cm * c))
    | _, _ => none
  | _, _ => none

/-- The `GG` expansion `O^{(x)}_GG = O_dot ∘ Ô^{(x)}_GG` of [I, Def 3.15] = [II, Def 4.5],
tracked: [I, (3.17)] if the solid edges attached to `x` are `G_{xy}`, `G_{y'x}`, its complex
conjugate if they are `Ḡ_{xy}`, `Ḡ_{y'x}`; the identity otherwise, if a `×`-dotted edge
`x ≠ y`, `x ≠ y'` is missing, or on graphs with a `P`/`Q` label, a `G^{(T)}` entry or a
`(G_{xx})⁻¹` or
`W_D` weight. -/
def oGGT {k n : ℕ} (x : Atom k n) (Γ : Graph k n) : TExpansion k n :=
  if !(Γ.comps.all Comp.isPlainB) then [Tracked.self Γ] else
  match ggPos x Γ with
  | some E => E.bind fun _ g => oDotT g
  | none =>
    match ggPos x Γ.conj with
    | some E => E.conj.bind fun _ g => oDotT g
    | none => [Tracked.self Γ]

/-- The `GG` expansion `O^{(x)}_GG` ([I, Def 3.15] = [II, Def 4.5]). -/
def oGG {k n : ℕ} (x : Atom k n) (Γ : Graph k n) : Expansion k := (oGGT x Γ).forget

/-- The `GḠ` expansion `O^{(x)}_GḠ` of [I, Def 3.18] = [II, Def 4.6], tracked: the multi-edge
expansion with `k₁ = k₂ = 1`, `k₃ = k₄ = 0` ([I, (3.19)]) or `k₁ = k₂ = 0`, `k₃ = k₄ = 1`, when the
solid edges attached to `x` are `G_{xy}`, `Ḡ_{xy'}` or `G_{yx}`, `Ḡ_{y'x}`; the identity
otherwise. -/
def oGGbarT {k n : ℕ} (x : Atom k n) (Γ : Graph k n) : TExpansion k n :=
  let out := ((Γ.edgeIdx x .plus true).length, (Γ.edgeIdx x .minus true).length)
  let inn := ((Γ.edgeIdx x .plus false).length, (Γ.edgeIdx x .minus false).length)
  if Γ.deg x == 2 && ((out == (1, 1) && inn == (0, 0)) || (out == (0, 0) && inn == (1, 1))) then
    oMultiET x Γ
  else [Tracked.self Γ]

/-- The `GḠ` expansion `O^{(x)}_GḠ` ([I, Def 3.18] = [II, Def 4.6]). -/
def oGGbar {k n : ℕ} (x : Atom k n) (Γ : Graph k n) : Expansion k := (oGGbarT x Γ).forget

/-! ## Products of component factors -/

section Values

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The product of the factors of the components `cs`. -/
private def pv {V : Type*} (D : Data ι) (σ : V → ι) (cs : List (Comp V)) : ℂ :=
  (cs.map (Comp.val D σ)).prod

/-- The product of the factors of the random components of `cs`. -/
private def rv {V : Type*} (D : Data ι) (σ : V → ι) (cs : List (Comp V)) : ℂ :=
  ((cs.filter fun c => c.kind.isRandom).map (Comp.val D σ)).prod

/-- The product of the factors of the deterministic components of `cs`. -/
private def dv {V : Type*} (D : Data ι) (σ : V → ι) (cs : List (Comp V)) : ℂ :=
  ((cs.filter fun c => !c.kind.isRandom).map (Comp.val D σ)).prod

variable {V W : Type*} (D : Data ι) (σ : V → ι)

@[simp] private theorem pv_nil : pv D σ ([] : List (Comp V)) = 1 := rfl

@[simp] private theorem pv_cons (c : Comp V) (cs : List (Comp V)) :
    pv D σ (c :: cs) = Comp.val D σ c * pv D σ cs := by
  simp [pv]

@[simp] private theorem pv_append (cs cs' : List (Comp V)) :
    pv D σ (cs ++ cs') = pv D σ cs * pv D σ cs' := by
  simp [pv]

@[simp] private theorem rv_nil : rv D σ ([] : List (Comp V)) = 1 := rfl

@[simp] private theorem rv_cons (c : Comp V) (cs : List (Comp V)) :
    rv D σ (c :: cs) = (if c.kind.isRandom then Comp.val D σ c else 1) * rv D σ cs := by
  unfold rv
  by_cases h : c.kind.isRandom <;> simp [h]

@[simp] private theorem rv_append (cs cs' : List (Comp V)) :
    rv D σ (cs ++ cs') = rv D σ cs * rv D σ cs' := by
  simp [rv]

@[simp] private theorem dv_nil : dv D σ ([] : List (Comp V)) = 1 := rfl

@[simp] private theorem dv_cons (c : Comp V) (cs : List (Comp V)) :
    dv D σ (c :: cs) = (if c.kind.isRandom then 1 else Comp.val D σ c) * dv D σ cs := by
  unfold dv
  by_cases h : c.kind.isRandom <;> simp [h]

@[simp] private theorem dv_append (cs cs' : List (Comp V)) :
    dv D σ (cs ++ cs') = dv D σ cs * dv D σ cs' := by
  simp [dv]

private theorem pv_eq (cs : List (Comp V)) : pv D σ cs = dv D σ cs * rv D σ cs := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [pv_cons, dv_cons, rv_cons, ih]
    split_ifs <;> ring

private theorem val_map (σ : W → ι) (f : V → W) (c : Comp V) :
    Comp.val D σ (c.map f) = Comp.val D (σ ∘ f) c := by
  simp only [Comp.val, Comp.map, List.map_map]
  rfl

private theorem rv_map (σ : W → ι) (f : V → W) (cs : List (Comp V)) :
    rv D σ (cs.map (Comp.map f)) = rv D (σ ∘ f) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [List.map_cons, rv_cons, rv_cons, ih, val_map]; rfl

private theorem dv_map (σ : W → ι) (f : V → W) (cs : List (Comp V)) :
    dv D σ (cs.map (Comp.map f)) = dv D (σ ∘ f) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [List.map_cons, dv_cons, dv_cons, ih, val_map]; rfl

@[simp] private theorem mkC_kind (κ : Kind) (u v : V) : (mkC κ u v).kind = κ := rfl

private theorem val_solidC [DecidableEq V] (ch : Charge) (u v : V) :
    Comp.val D σ (solidC ch u v) = ch.apply (D.Gm ∅ (σ u) (σ v)) := by
  unfold solidC
  split_ifs with h
  · subst h
    simp [mkC, Comp.val]
  · simp [mkC, Comp.val]

end Values

/-! ## Atom labellings of graphs with new atoms -/

section Labellings

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k n j : ℕ}

omit [Fintype ι] [DecidableEq ι] in
@[simp] private theorem elim_append_liftA (e : Fin k → ι) (s : Fin n → ι) (a : Fin j → ι)
    (u : Atom k n) : Sum.elim e (Fin.append s a) (liftA j u) = Sum.elim e s u := by
  rcases u with i | i <;> simp [liftA, Fin.append_left]

omit [Fintype ι] [DecidableEq ι] in
@[simp] private theorem elim_append_newA (e : Fin k → ι) (s : Fin n → ι) (a : Fin j → ι)
    (i : Fin j) : Sum.elim e (Fin.append s a) (newA i) = a i := by
  simp [newA, Fin.append_right]

omit [Fintype ι] [DecidableEq ι] in
@[simp] private theorem elim_append_comp_liftA (e : Fin k → ι) (s : Fin n → ι) (a : Fin j → ι) :
    Sum.elim e (Fin.append s a) ∘ liftA j = Sum.elim e s := by
  funext u
  simp

/-- The value of a graph with `j` more internal atoms, the labels of the new atoms summed
last. -/
private theorem valR_split {Ω : Type} (g : Graph k (n + j)) (PF : PFamily Ω ι) (D : Ω → Data ι)
    (e : Fin k → ι) (ω : Ω) :
    g.valR PF D e ω =
      ∑ s : Fin n → ι, ∑ a : Fin j → ι, g.termR PF D (Sum.elim e (Fin.append s a)) ω := by
  unfold Graph.valR
  rw [← (Fin.appendEquiv n j).sum_comp, Fintype.sum_prod_type]
  rfl

omit [DecidableEq ι] in
/-- A sum over the labellings of one atom is a sum over `ι`. -/
private theorem sum_fin1 (f : (Fin 1 → ι) → ℂ) : ∑ a, f a = ∑ α, f ![α] := by
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι) _ _ fun a => ?_
  congr 1
  funext i
  fin_cases i
  rfl

omit [DecidableEq ι] in
/-- A sum over the labellings of two atoms is a double sum. -/
private theorem sum_fin2 (f : (Fin 2 → ι) → ℂ) : ∑ a, f a = ∑ α, ∑ β, f ![α, β] := by
  rw [← (piFinTwoEquiv fun _ => ι).symm.sum_comp, Fintype.sum_prod_type]
  rfl

end Labellings

/-! ## Terms of unlabelled graphs and of graphs with one label `Q_u` -/

section TermR

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Ω : Type} {k N : ℕ}

private theorem dedup_singleton {α : Type*} [DecidableEq α] (l : List α) (a : α)
    (h1 : ∀ x ∈ l, x = a) (h2 : a ∈ l) : l.dedup = [a] := by
  have hnd := List.nodup_dedup l
  have hmem : ∀ x, x ∈ l.dedup ↔ x ∈ l := fun x => List.mem_dedup
  cases hd : l.dedup with
  | nil => exact absurd ((hmem a).2 h2) (by rw [hd]; simp)
  | cons x rest =>
    rw [hd] at hnd
    have hx : x = a := h1 x ((hmem x).1 (by rw [hd]; simp))
    have hrest : rest = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro y hy
      have hya : y = a := h1 y ((hmem y).1 (by rw [hd]; simp [hy]))
      exact (List.nodup_cons.1 hnd).1 (by rw [hx, ← hya]; exact hy)
    rw [hrest, hx]

/-- The term of a graph without labels. -/
private theorem termR_unl (g : Graph k N) (h : ∀ c ∈ g.comps, c.label = none)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (σ : Atom k N → ι) (ω : Ω) :
    g.termR PF D σ ω = g.coeff.eval (D ω).m * pv (D ω) σ g.comps := by
  have h1 : g.comps.filter (fun c => c.label.isNone) = g.comps :=
    List.filter_eq_self.2 fun c hc => by simp [h c hc]
  have h2 : g.labels = [] := by
    unfold Graph.labels
    rw [List.filterMap_eq_nil_iff.2 fun c hc => h c hc]
    rfl
  simp [Graph.termR, h1, h2, pv]

private theorem labelQs_none {V : Type*} (D₀ : Data ι) (σ : V → ι) (u : V) (cs : List (Comp V))
    (h : ∀ c ∈ cs, c.label = none) :
    (((labelQs u cs).filter fun c => c.label.isNone).map (Comp.val D₀ σ)).prod = dv D₀ σ cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have ih' := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    have hc := h c (List.mem_cons_self ..)
    simp only [labelQs, List.map_cons, Comp.labelQ] at ih' ⊢
    by_cases hr : c.kind.isRandom
    · simp [hr, ih']
    · simp [hr, hc, ih']

private theorem labelQs_some {V : Type*} [DecidableEq V] (D₀ : Data ι) (σ : V → ι) (u : V)
    (cs : List (Comp V))
    (h : ∀ c ∈ cs, c.label = none) :
    (((labelQs u cs).filter fun c => decide (c.label = some (.Q, u))).map
      (Comp.val D₀ σ)).prod = rv D₀ σ cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have ih' := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    have hc := h c (List.mem_cons_self ..)
    simp only [labelQs, List.map_cons, Comp.labelQ] at ih' ⊢
    by_cases hr : c.kind.isRandom
    · simp only [hr, ite_true, List.filter_cons, decide_true, rv_cons, List.map_cons,
        List.prod_cons, ih']
      rfl
    · simp [hr, hc, ih']

private theorem labelQs_labels {V : Type*} [DecidableEq V] (u : V) (cs : List (Comp V))
    (h : ∀ c ∈ cs, c.label = none) (hr : ∃ c ∈ cs, c.kind.isRandom = true) :
    ((labelQs u cs).filterMap Comp.label).dedup = [(.Q, u)] := by
  apply dedup_singleton
  · intro l hl
    obtain ⟨c', hc', hl'⟩ := List.mem_filterMap.1 hl
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    unfold Comp.labelQ at hl'
    split_ifs at hl' with hcr
    · exact (Option.some.inj hl').symm
    · rw [h c hc] at hl'
      exact absurd hl' (by simp)
  · obtain ⟨c, hc, hcr⟩ := hr
    exact List.mem_filterMap.2 ⟨Comp.labelQ u c, List.mem_map.2 ⟨c, hc, rfl⟩,
      by simp [Comp.labelQ, hcr]⟩

/-- The term of a graph `𝒢₀ Q_u(𝒢₁)` whose labelled part is `labelQs u cs`. -/
private theorem termR_Q (u : Atom k N) (cs ds : List (Comp (Atom k N))) (d : Coeff)
    (hcs : ∀ c ∈ cs, c.label = none) (hds : ∀ c ∈ ds, c.label = none)
    (hr : ∃ c ∈ cs, c.kind.isRandom = true)
    (PF : PFamily Ω ι) (D : Ω → Data ι) (σ : Atom k N → ι) (ω : Ω) :
    (⟨labelQs u cs ++ ds, d⟩ : Graph k N).termR PF D σ ω =
      d.eval (D ω).m * dv (D ω) σ cs * pv (D ω) σ ds *
        PF.op .Q (σ u) (fun ω' => rv (D ω') σ cs) ω := by
  have hl : (⟨labelQs u cs ++ ds, d⟩ : Graph k N).labels = [(.Q, u)] := by
    unfold Graph.labels
    rw [List.filterMap_append, List.filterMap_eq_nil_iff.2 fun c hc => hds c hc, List.append_nil]
    exact labelQs_labels u cs hcs hr
  have h1 : ∀ D₀ : Data ι, ((ds.filter fun c => c.label.isNone).map (Comp.val D₀ σ)).prod =
      pv D₀ σ ds := fun D₀ => by
    rw [List.filter_eq_self.2 fun c hc => by simp [hds c hc]]
    rfl
  have h2 : ds.filter (fun c => decide (c.label = some (.Q, u))) = [] :=
    List.filter_eq_nil_iff.2 fun c hc => by simp [hds c hc]
  simp only [Graph.termR, hl, List.filter_append, List.map_append, List.prod_append,
    labelQs_none _ _ u cs hcs, h1, h2, List.map_nil, List.prod_nil, mul_one, List.map_cons,
    List.prod_cons, labelQs_some _ _ u cs hcs]
  ring

end TermR

/-! ## Closure of the test functions and linearity of `P_x` -/

section TestClosure

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D)

private theorem test_mul' {f g : Ω → ℂ} (hf : A.Test f) (hg : A.Test g) :
    A.Test fun ω => f ω * g ω :=
  A.test_mul f g hf hg

private theorem test_add' {f g : Ω → ℂ} (hf : A.Test f) (hg : A.Test g) :
    A.Test fun ω => f ω + g ω :=
  A.test_add f g hf hg

private theorem test_const' (c : ℂ) : A.Test fun _ => c := A.test_const c

private theorem test_sub' {f g : Ω → ℂ} (hf : A.Test f) (hg : A.Test g) :
    A.Test fun ω => f ω - g ω := by
  have e : (fun ω => f ω - g ω) = fun ω => f ω + (-1 : ℂ) * g ω := funext fun ω => by ring
  rw [e]
  exact test_add' A hf (test_mul' A (test_const' A _) hg)

private theorem test_neg' {f : Ω → ℂ} (hf : A.Test f) : A.Test fun ω => -f ω := by
  have e : (fun ω => -f ω) = fun ω => (-1 : ℂ) * f ω := funext fun ω => by ring
  rw [e]
  exact test_mul' A (test_const' A _) hf

private theorem test_star' {f : Ω → ℂ} (hf : A.Test f) : A.Test fun ω => star (f ω) :=
  A.test_star f hf

private theorem test_G (a b : ι) : A.Test fun ω => A.G ω a b := by
  have h := A.test_entry a b
  have e : (fun ω => (D ω).Gm ∅ a b) = fun ω => A.G ω a b :=
    funext fun ω => by rw [A.data_G]; rfl
  rwa [e] at h

private theorem test_dh' (a b : ι) {F : Ω → ℂ} (hF : A.Test F) :
    A.Test fun ω => A.dh a b F ω :=
  A.test_dh a b F hF

private theorem test_listProd' {β : Type*} (l : List β) {f : β → Ω → ℂ}
    (h : ∀ q ∈ l, A.Test (f q)) :
    A.Test fun ω => (l.map fun q => f q ω).prod := by
  induction l with
  | nil => simpa using test_const' A 1
  | cons y l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact test_mul' A (h y (List.mem_cons_self ..)) (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

end TestClosure

/-- Proves `A.Test f` for `f` built from resolvent entries, conjugates, derivatives, sums,
products and constants. -/
local macro "test_tac" A:term : tactic =>
  `(tactic| repeat' (first
    | with_reducible assumption
    | with_reducible apply test_G $A
    | with_reducible apply test_dh' $A
    | with_reducible apply test_star' $A
    | with_reducible apply test_mul' $A
    | with_reducible apply test_sub' $A
    | with_reducible apply test_add' $A
    | with_reducible apply test_neg' $A
    | with_reducible apply test_sum' $A
    | with_reducible apply test_const' $A
    | intro))

/-- Proves `A.Good f` for a test function `f`. -/
local macro "good_tac" A:term : tactic =>
  `(tactic| (apply ($A).test_good; test_tac $A))

section Aux

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D)

private theorem P_add' {f g : Ω → ℂ} (hf : A.Good f) (hg : A.Good g) (x : ι) (ω : Ω) :
    PF.P x (fun ω => f ω + g ω) ω = PF.P x f ω + PF.P x g ω :=
  congrFun (A.laws.add x f g hf hg) ω

private theorem P_cmul' {f : Ω → ℂ} (c : ℂ) (hf : A.Good f) (x : ι) (ω : Ω) :
    PF.P x (fun ω => c * f ω) ω = c * PF.P x f ω :=
  congrFun (A.laws.smul x c f hf) ω

include A in
private theorem P_zero' (x : ι) (ω : Ω) : PF.P x (fun _ => 0) ω = 0 := by
  have h := P_cmul' A 0 (A.laws.good_const 0) x ω
  simpa using h

private theorem P_neg' {f : Ω → ℂ} (hf : A.Good f) (x : ι) (ω : Ω) :
    PF.P x (fun ω => -f ω) ω = -PF.P x f ω := by
  have h := P_cmul' A (-1) hf x ω
  simpa using h

private theorem P_sub' {f g : Ω → ℂ} (hf : A.Good f) (hg : A.Good g) (x : ι) (ω : Ω) :
    PF.P x (fun ω => f ω - g ω) ω = PF.P x f ω - PF.P x g ω := by
  have hg' : A.Good fun ω => -g ω := by
    have e : (fun ω => -g ω) = fun ω => (-1 : ℂ) * g ω := funext fun ω => by ring
    rw [e]
    exact A.laws.good_mul _ _ (A.laws.good_const _) hg
  have h := P_add' A hf hg' x ω
  rw [P_neg' A hg x ω] at h
  simpa [sub_eq_add_neg] using h

private theorem good_sum' {κ : Type} (s : Finset κ) {f : κ → Ω → ℂ} (h : ∀ i, A.Good (f i)) :
    A.Good fun ω => ∑ i ∈ s, f i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using A.laws.good_const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact A.laws.good_add _ _ (h a) ih

private theorem P_sum' {κ : Type} (s : Finset κ) {f : κ → Ω → ℂ} (h : ∀ i, A.Good (f i))
    (x : ι) (ω : Ω) :
    PF.P x (fun ω => ∑ i ∈ s, f i ω) ω = ∑ i ∈ s, PF.P x (f i) ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using P_zero' A x ω
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [P_add' A (h a) (good_sum' A s h) x ω, ih]

omit [Fintype ι] [DecidableEq ι] in
private theorem P_congr' {f g : Ω → ℂ} (h : ∀ ω, f ω = g ω) (x : ι) :
    PF.P x f = PF.P x g := by
  rw [funext h]

private theorem P_listSum' {β : Type*} (l : List β) {f : β → Ω → ℂ} (h : ∀ q ∈ l, A.Good (f q))
    (x : ι) (ω : Ω) :
    PF.P x (fun ω => (l.map fun q => f q ω).sum) ω = (l.map fun q => PF.P x (f q) ω).sum := by
  induction l with
  | nil => simpa using P_zero' A x ω
  | cons y l ih =>
    have hg : A.Good fun ω => (l.map fun q => f q ω).sum := by
      clear ih
      induction l with
      | nil => simpa using A.laws.good_const 0
      | cons z l ih' =>
        simp only [List.map_cons, List.sum_cons]
        exact A.laws.good_add _ _ (h z (by simp)) (ih' fun q hq => h q (by
          simp only [List.mem_cons] at hq ⊢; tauto))
    simp only [List.map_cons, List.sum_cons]
    rw [P_add' A (h y (List.mem_cons_self ..)) hg, ih fun q hq => h q (List.mem_cons_of_mem _ hq)]

private theorem dh_mul' (a b : ι) {f g : Ω → ℂ} (hf : A.Test f) (hg : A.Test g) :
    A.dh a b (fun ω => f ω * g ω) = fun ω => A.dh a b f ω * g ω + f ω * A.dh a b g ω :=
  A.dh_mul a b f g hf hg

private theorem dh_G (a b x y : ι) :
    A.dh a b (fun ω => A.G ω x y) = fun ω => -(A.G ω x a * A.G ω b y) :=
  A.dh_green a b x y


private theorem H_mul_G (ω : Ω) (a b : ι) :
    ∑ β, A.H ω a β * A.G ω β b = (if a = b then 1 else 0) + A.z * A.G ω a b := by
  have hz : A.z.im ≠ 0 := ne_of_gt A.im_pos
  have h := congrFun (congrFun (sub_mul_green (A.isHermitian ω) hz) a) b
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, sub_mul,
    Finset.sum_sub_distrib, smul_eq_mul, ite_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
  unfold ModelAdm.G
  linear_combination h

private theorem G_mul_H (ω : Ω) (a b : ι) :
    ∑ β, A.G ω a β * A.H ω β b = (if a = b then 1 else 0) + A.z * A.G ω a b := by
  have hz : A.z.im ≠ 0 := ne_of_gt A.im_pos
  have h := congrFun (congrFun (green_mul_sub (A.isHermitian ω) hz) a) b
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, mul_sub,
    Finset.sum_sub_distrib, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  unfold ModelAdm.G
  linear_combination h

private theorem rowSum' (p : ι) : ∑ β, (A.S p β : ℂ) = 1 := by
  have h := A.rowSum p
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h

private theorem S_symm' (a b : ι) : (A.S a b : ℂ) = (A.S b a : ℂ) := by
  rw [A.isSymm.apply b a]

/-! ### One integration by parts in a row or a column -/

/-- The expansion `G_{pb} = m δ_{pb} - m² G_{pb} - m ∑_β h_{pβ} G_{βb}` followed by Gaussian
integration by parts in `P_p` ([I, (3.8)], [I, Lemma 2.4]). -/
private theorem ibp_row (p b : ι) {K : Ω → ℂ} (hK : A.Test K) (ω : Ω) :
    PF.P p (fun ω => A.G ω p b * K ω) ω =
      msc A.z * (if p = b then 1 else 0) * PF.P p K ω
      + msc A.z * ∑ β, (A.S p β : ℂ) *
          PF.P p (fun ω => (A.G ω β β - msc A.z) * A.G ω p b * K ω) ω
      - msc A.z * ∑ β, (A.S p β : ℂ) * PF.P p (fun ω => A.G ω β b * A.dh β p K ω) ω := by
  set m := msc A.z with hm
  have hmz : m * (m + A.z) = -1 := msc_mul A.z
  have hpt : ∀ ω, A.G ω p b * K ω = -m ^ 2 * (A.G ω p b * K ω) +
      (m * (if p = b then 1 else 0)) * K ω + (-m) * ∑ β, A.H ω p β * (A.G ω β b * K ω) := by
    intro ω
    have h := H_mul_G A ω p b
    have e : ∑ β, A.H ω p β * (A.G ω β b * K ω) = (∑ β, A.H ω p β * A.G ω β b) * K ω := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun β _ => by ring
    rw [e, h]
    linear_combination (A.G ω p b * K ω) * hmz
  have hGH : ∀ β, A.Good fun ω => A.H ω p β * (A.G ω β b * K ω) := fun β =>
    A.laws.good_mul _ _ (A.good_H p β) (by good_tac A)
  have hibp : ∀ β, PF.P p (fun ω => A.H ω p β * (A.G ω β b * K ω)) ω =
      (A.S p β : ℂ) * (-PF.P p (fun ω => A.G ω β β * A.G ω p b * K ω) ω +
        PF.P p (fun ω => A.G ω β b * A.dh β p K ω) ω) := by
    intro β
    rw [A.ibp p p β (Or.inl rfl) (fun ω => A.G ω β b * K ω) (by test_tac A)]
    beta_reduce
    rw [dh_mul' A β p (test_G A β b) hK, dh_G]
    beta_reduce
    rw [P_add' A (by good_tac A) (by good_tac A), ← P_neg' A (by good_tac A)]
    congr 3
    funext ω
    ring
  have hX : PF.P p (fun ω => A.G ω p b * K ω) ω =
      -m ^ 2 * PF.P p (fun ω => A.G ω p b * K ω) ω + (m * (if p = b then 1 else 0)) *
        PF.P p K ω + (-m) * ∑ β, (A.S p β : ℂ) *
          (-PF.P p (fun ω => A.G ω β β * A.G ω p b * K ω) ω +
            PF.P p (fun ω => A.G ω β b * A.dh β p K ω) ω) := by
    conv_lhs => rw [P_congr' hpt p]
    rw [P_add' A (by good_tac A)
        (by exact A.laws.good_mul _ _ (A.laws.good_const _) (good_sum' A _ hGH)),
      P_add' A (by good_tac A) (by good_tac A), P_cmul' A _ (by good_tac A),
      P_cmul' A _ (A.test_good _ hK), P_cmul' A _ (good_sum' A _ hGH), P_sum' A _ hGH]
    simp only [hibp]
  have hsplit : ∀ β, PF.P p (fun ω => (A.G ω β β - m) * A.G ω p b * K ω) ω =
      PF.P p (fun ω => A.G ω β β * A.G ω p b * K ω) ω -
        m * PF.P p (fun ω => A.G ω p b * K ω) ω := by
    intro β
    rw [P_congr' (g := fun ω => A.G ω β β * A.G ω p b * K ω - m * (A.G ω p b * K ω))
      (fun ω => by ring), P_sub' A (by good_tac A) (by good_tac A), P_cmul' A _ (by good_tac A)]
  simp only [hsplit]
  have hs := rowSum' A p
  simp only [mul_sub, mul_add, mul_neg, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib] at hX ⊢
  rw [← Finset.sum_mul, hs]
  linear_combination hX

/-- The expansion `G_{ap} = m δ_{ap} - m² G_{ap} - m ∑_β G_{aβ} h_{βp}` followed by Gaussian
integration by parts in `P_p` ([I, (3.8)], [I, Lemma 2.4]). -/
private theorem ibp_col (p a : ι) {K : Ω → ℂ} (hK : A.Test K) (ω : Ω) :
    PF.P p (fun ω => A.G ω a p * K ω) ω =
      msc A.z * (if a = p then 1 else 0) * PF.P p K ω
      + msc A.z * ∑ β, (A.S p β : ℂ) *
          PF.P p (fun ω => (A.G ω β β - msc A.z) * A.G ω a p * K ω) ω
      - msc A.z * ∑ β, (A.S p β : ℂ) * PF.P p (fun ω => A.G ω a β * A.dh p β K ω) ω := by
  set m := msc A.z with hm
  have hmz : m * (m + A.z) = -1 := msc_mul A.z
  have hpt : ∀ ω, A.G ω a p * K ω = -m ^ 2 * (A.G ω a p * K ω) +
      (m * (if a = p then 1 else 0)) * K ω + (-m) * ∑ β, A.H ω β p * (A.G ω a β * K ω) := by
    intro ω
    have h := G_mul_H A ω a p
    have e : ∑ β, A.H ω β p * (A.G ω a β * K ω) = (∑ β, A.G ω a β * A.H ω β p) * K ω := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun β _ => by ring
    rw [e, h]
    linear_combination (A.G ω a p * K ω) * hmz
  have hGH : ∀ β, A.Good fun ω => A.H ω β p * (A.G ω a β * K ω) := fun β =>
    A.laws.good_mul _ _ (A.good_H β p) (by good_tac A)
  have hibp : ∀ β, PF.P p (fun ω => A.H ω β p * (A.G ω a β * K ω)) ω =
      (A.S p β : ℂ) * (-PF.P p (fun ω => A.G ω β β * A.G ω a p * K ω) ω +
        PF.P p (fun ω => A.G ω a β * A.dh p β K ω) ω) := by
    intro β
    rw [A.ibp p β p (Or.inr rfl) (fun ω => A.G ω a β * K ω) (by test_tac A)]
    beta_reduce
    rw [dh_mul' A p β (test_G A a β) hK, dh_G, S_symm' A β p]
    beta_reduce
    rw [P_add' A (by good_tac A) (by good_tac A), ← P_neg' A (by good_tac A)]
    congr 3
    funext ω
    ring
  have hX : PF.P p (fun ω => A.G ω a p * K ω) ω =
      -m ^ 2 * PF.P p (fun ω => A.G ω a p * K ω) ω + (m * (if a = p then 1 else 0)) *
        PF.P p K ω + (-m) * ∑ β, (A.S p β : ℂ) *
          (-PF.P p (fun ω => A.G ω β β * A.G ω a p * K ω) ω +
            PF.P p (fun ω => A.G ω a β * A.dh p β K ω) ω) := by
    conv_lhs => rw [P_congr' hpt p]
    rw [P_add' A (by good_tac A)
        (by exact A.laws.good_mul _ _ (A.laws.good_const _) (good_sum' A _ hGH)),
      P_add' A (by good_tac A) (by good_tac A), P_cmul' A _ (by good_tac A),
      P_cmul' A _ (A.test_good _ hK), P_cmul' A _ (good_sum' A _ hGH), P_sum' A _ hGH]
    simp only [hibp]
  have hsplit : ∀ β, PF.P p (fun ω => (A.G ω β β - m) * A.G ω a p * K ω) ω =
      PF.P p (fun ω => A.G ω β β * A.G ω a p * K ω) ω -
        m * PF.P p (fun ω => A.G ω a p * K ω) ω := by
    intro β
    rw [P_congr' (g := fun ω => A.G ω β β * A.G ω a p * K ω - m * (A.G ω a p * K ω))
      (fun ω => by ring), P_sub' A (by good_tac A) (by good_tac A), P_cmul' A _ (by good_tac A)]
  simp only [hsplit]
  have hs := rowSum' A p
  simp only [mul_sub, mul_add, mul_neg, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib] at hX ⊢
  rw [← Finset.sum_mul, hs]
  linear_combination hX

omit [Fintype ι] [DecidableEq ι] in
private theorem Q_apply' (x : ι) (f : Ω → ℂ) (ω : Ω) :
    PF.op .Q x f ω = f ω - PF.P x f ω := rfl

end Aux

/-! ## Factors of components under the model relations -/

/-- A component without minor that is not a `(G_{xx})⁻¹` or `W_D` weight. -/
private def basB {V : Type*} (c : Comp V) : Bool :=
  c.minor.isEmpty &&
    match c.kind with
    | .inv _ | .wD _ _ => false
    | _ => true

private theorem basB_map {V W : Type*} (f : V → W) (c : Comp V) : basB (c.map f) = basB c := by
  simp [basB, Comp.map]

private theorem basB_of_plain {V : Type*} {c : Comp V} (h : c.isPlainB = true) :
    basB c = true ∧ c.label = none := by
  rcases c with ⟨κ, x, y, mi, l⟩
  simp only [Comp.isPlainB, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, h2⟩
  rw [basB, h1, Bool.true_and]
  exact h3

section ModelVal

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D)

private theorem Gm_eq (ω : Ω) (a b : ι) : (D ω).Gm ∅ a b = A.G ω a b := by
  rw [A.data_G]
  rfl

private theorem m_eq (ω : Ω) : (D ω).m = msc A.z := A.data_m ω

private theorem S_eq (ω : Ω) (a b : ι) : (D ω).S a b = (A.S a b : ℂ) := by
  rw [A.data_S]
  rfl

private theorem val_G {V : Type*} (σ : V → ι) (ω : Ω) (ch : Charge) (x y : V) :
    Comp.val (D ω) σ (mkC (.G ch) x y) = ch.apply (A.G ω (σ x) (σ y)) := by
  simp [mkC, Comp.val, Gm_eq A]

private theorem val_weight {V : Type*} (σ : V → ι) (ω : Ω) (ch : Charge) (x y : V) :
    Comp.val (D ω) σ (mkC (.weight ch) x y) = ch.apply (A.G ω (σ x) (σ x)) := by
  simp [mkC, Comp.val, Gm_eq A]

private theorem val_light {V : Type*} (σ : V → ι) (ω : Ω) (ch : Charge) (x y : V) :
    Comp.val (D ω) σ (mkC (.light ch) x y) = ch.apply (A.G ω (σ x) (σ x) - msc A.z) := by
  simp [mkC, Comp.val, Gm_eq A, m_eq A]

private theorem val_s {V : Type*} (σ : V → ι) (ω : Ω) (x y : V) :
    Comp.val (D ω) σ (mkC (.waved .s) x y) = (A.S (σ x) (σ y) : ℂ) := by
  simp [mkC, Comp.val, S_eq A]

private theorem val_Sp {V : Type*} (σ : V → ι) (ω : Ω) (x y : V) :
    Comp.val (D ω) σ (mkC (.waved .plus) x y) = (D ω).Sp (σ x) (σ y) := by
  simp [mkC, Comp.val]

private theorem val_solid {V : Type*} [DecidableEq V] (σ : V → ι) (ω : Ω) (ch : Charge)
    (x y : V) : Comp.val (D ω) σ (solidC ch x y) = ch.apply (A.G ω (σ x) (σ y)) := by
  rw [val_solidC, Gm_eq A]

private theorem dh_G' (a b x y : ι) :
    A.dh a b (fun ω => A.G ω x y) = fun ω => -(A.G ω x a * A.G ω b y) :=
  A.dh_green a b x y

private theorem dh_starG' (a b x y : ι) :
    A.dh a b (fun ω => star (A.G ω x y)) = fun ω => -(star (A.G ω x b) * star (A.G ω a y)) :=
  A.dh_conj_green a b x y

/-- The factor of a random component without minor is a test function. -/
private theorem val_test {V : Type*} (σ : V → ι) (c : Comp V) (hb : basB c = true)
    (hr : c.kind.isRandom = true) : A.Test fun ω => Comp.val (D ω) σ c := by
  rcases c with ⟨κ, x, y, mi, l⟩
  simp only [basB, Bool.and_eq_true, List.isEmpty_iff] at hb
  obtain ⟨rfl, hk⟩ := hb
  rw [show (fun ω => Comp.val (D ω) σ ⟨κ, x, y, [], l⟩) =
    fun ω => Comp.val (D ω) σ (mkC κ x y) from rfl]
  cases κ with
  | G ch =>
    simp only [val_G A]
    cases ch
    · exact test_G A _ _
    · exact test_star' A (test_G A _ _)
  | weight ch =>
    simp only [val_weight A]
    cases ch
    · exact test_G A _ _
    · exact test_star' A (test_G A _ _)
  | light ch =>
    simp only [val_light A]
    cases ch
    · exact test_sub' A (test_G A _ _) (test_const' A _)
    · exact test_star' A (test_sub' A (test_G A _ _) (test_const' A _))
  | inv ch => simp at hk
  | wD ch d => simp at hk
  | _ => simp [Kind.isRandom] at hr

/-- The product of the random factors of components without minors is a test function. -/
private theorem rv_test {V : Type*} (σ : V → ι) (cs : List (Comp V))
    (hb : ∀ c ∈ cs, basB c = true) : A.Test fun ω => rv (D ω) σ cs := by
  induction cs with
  | nil => simpa using test_const' A 1
  | cons c cs ih =>
    simp only [rv_cons]
    refine test_mul' A ?_ (ih fun c hc => hb c (List.mem_cons_of_mem _ hc))
    by_cases hr : c.kind.isRandom
    · simp only [hr, ite_true]
      exact val_test A σ c (hb c (List.mem_cons_self ..)) hr
    · simp only [hr]
      exact test_const' A 1

/-- `-∂_{h_{pq}}` of the factor of a random component is the product of the factors of
`Comp.dPieces p q` ([I, (3.8)]). -/
private theorem dPieces_spec {V : Type*} [DecidableEq V] (σ : V → ι) (p q : V) (c : Comp V)
    (hb : basB c = true) (hr : c.kind.isRandom = true) :
    ∃ ps, c.dPieces p q = some ps ∧ (∀ c' ∈ ps, basB c' = true ∧ c'.label = none ∧
      c'.kind.isRandom = true) ∧
      A.dh (σ p) (σ q) (fun ω => Comp.val (D ω) σ c) = fun ω => -(rv (D ω) σ ps) := by
  rcases c with ⟨κ, x, y, mi, l⟩
  simp only [basB, Bool.and_eq_true, List.isEmpty_iff] at hb
  obtain ⟨rfl, hk⟩ := hb
  rw [show (fun ω => Comp.val (D ω) σ ⟨κ, x, y, [], l⟩) =
    fun ω => Comp.val (D ω) σ (mkC κ x y) from rfl]
  have hsol : ∀ (ch : Charge) (u v : V), basB (solidC ch u v) = true ∧
      (solidC ch u v).label = none ∧ (solidC ch u v).kind.isRandom = true := by
    intro ch u v
    unfold solidC
    split_ifs <;> simp [basB, mkC, Kind.isRandom]
  have hG : ∀ a b, (fun ω => A.G ω a b) = fun ω => green (A.H ω) A.z a b := fun _ _ => rfl
  cases κ with
  | G ch =>
    cases ch
    · refine ⟨_, rfl, by simpa using ⟨hsol _ _ _, hsol _ _ _⟩, ?_⟩
      simp only [val_G A, Charge.apply, rv_cons, rv_nil, (hsol _ _ _).2.2, ite_true, mul_one,
        val_solid A, dh_G' A]
      funext ω; simp [Kind.isWeight]
    · refine ⟨_, rfl, by simpa using ⟨hsol _ _ _, hsol _ _ _⟩, ?_⟩
      simp only [val_G A, Charge.apply, rv_cons, rv_nil, (hsol _ _ _).2.2, ite_true, mul_one,
        val_solid A, dh_starG' A]
      funext ω; simp [Kind.isWeight]
  | weight ch =>
    cases ch
    · refine ⟨_, rfl, by simpa using ⟨hsol _ _ _, hsol _ _ _⟩, ?_⟩
      simp only [val_weight A, Charge.apply, rv_cons, rv_nil, (hsol _ _ _).2.2, ite_true,
        mul_one, val_solid A, dh_G' A, Kind.isWeight, ite_true]
    · refine ⟨_, rfl, by simpa using ⟨hsol _ _ _, hsol _ _ _⟩, ?_⟩
      simp only [val_weight A, Charge.apply, rv_cons, rv_nil, (hsol _ _ _).2.2, ite_true,
        mul_one, val_solid A, dh_starG' A, Kind.isWeight, ite_true]
  | light ch =>
    have hdc : ∀ (F : Ω → ℂ) (a : ℂ), A.Test F →
        A.dh (σ p) (σ q) (fun ω => F ω - a) = A.dh (σ p) (σ q) F := by
      intro F a hF
      rw [show (fun ω => F ω - a) = F + fun _ => -a from funext fun ω => by simp [sub_eq_add_neg],
        A.dh_add _ _ _ _ hF (A.test_const _), A.dh_const, add_zero]
    cases ch
    · refine ⟨_, rfl, by simpa using ⟨hsol _ _ _, hsol _ _ _⟩, ?_⟩
      simp only [val_light A, Charge.apply, rv_cons, rv_nil, (hsol _ _ _).2.2, ite_true,
        mul_one, val_solid A, Kind.isWeight, ite_true]
      rw [hdc _ _ (test_G A _ _), dh_G' A]
    · refine ⟨_, rfl, by simpa using ⟨hsol _ _ _, hsol _ _ _⟩, ?_⟩
      simp only [val_light A, Charge.apply, rv_cons, rv_nil, (hsol _ _ _).2.2, ite_true,
        mul_one, val_solid A, Kind.isWeight, ite_true, star_sub]
      rw [hdc _ _ (test_star' A (test_G A _ _)), dh_starG' A]
  | inv ch => simp at hk
  | wD ch d => simp at hk
  | _ => simp [Kind.isRandom] at hr

end ModelVal

private theorem dv_rand {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type*} (D₀ : Data ι)
    (σ : V → ι) (ps : List (Comp V)) (h : ∀ c ∈ ps, c.kind.isRandom = true) : dv D₀ σ ps = 1 := by
  induction ps with
  | nil => rfl
  | cons c ps ih =>
    rw [dv_cons, ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')]
    simp [h c (List.mem_cons_self ..)]

private theorem dTerms_cons {V : Type*} [DecidableEq V] (p q : V) (c : Comp V)
    (cs : List (Comp V)) :
    dTerms p q (c :: cs) =
      ((c.dPieces p q).map fun ps => cs ++ ps).toList ++ (dTerms p q cs).map (c :: ·) := by
  unfold dTerms
  erw [List.finRange_succ]
  rw [List.filterMap_cons, List.filterMap_map, List.map_filterMap]
  cases h : c.dPieces p q <;> simp [h, Option.map_map, Function.comp_def]

private theorem dPieces_none {V : Type*} [DecidableEq V] (p q : V) (c : Comp V)
    (hb : basB c = true) (hr : c.kind.isRandom = false) : c.dPieces p q = none := by
  rcases c with ⟨κ, x, y, mi, l⟩
  cases κ <;> simp_all [Comp.dPieces, Kind.isRandom]

section DTerms

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D)

/-- The product rule behind `dTerms`: the sum of the random parts of the graphs of
`dTerms p q cs` is `-∂_{h_{pq}}` of the random part of `cs`; the deterministic parts are those
of `cs`. -/
private theorem dTerms_spec {V : Type*} [DecidableEq V] (σ : V → ι) (p q : V)
    (cs : List (Comp V)) (hb : ∀ c ∈ cs, basB c = true ∧ c.label = none) :
    (∀ d ∈ dTerms p q cs, (∀ c ∈ d, basB c = true ∧ c.label = none) ∧
      ∀ D₀ : Data ι, dv D₀ σ d = dv D₀ σ cs) ∧
    ∀ ω, ((dTerms p q cs).map fun d => rv (D ω) σ d).sum =
      -A.dh (σ p) (σ q) (fun ω' => rv (D ω') σ cs) ω := by
  induction cs with
  | nil =>
    refine ⟨by simp [dTerms], fun ω => ?_⟩
    simp only [dTerms, List.length_nil, List.finRange_zero, List.filterMap_nil, List.map_nil,
      List.sum_nil]
    rw [show (fun ω' => rv (D ω') σ ([] : List (Comp V))) = fun _ => (1 : ℂ) from rfl,
      A.dh_const]
    simp
  | cons c cs ih =>
    have hbc := hb c (List.mem_cons_self ..)
    obtain ⟨ih1, ih2⟩ := ih fun c hc => hb c (List.mem_cons_of_mem _ hc)
    have hcs : ∀ c ∈ cs, basB c = true := fun c hc => (hb c (List.mem_cons_of_mem _ hc)).1
    by_cases hr : c.kind.isRandom
    · obtain ⟨ps, hps, hps1, hps2⟩ := dPieces_spec A σ p q c hbc.1 hr
      rw [dTerms_cons, hps]
      refine ⟨?_, fun ω => ?_⟩
      · intro d hd
        simp only [Option.map_some, Option.toList_some, List.singleton_append, List.mem_cons,
          List.mem_map] at hd
        rcases hd with rfl | ⟨d', hd', rfl⟩
        · refine ⟨fun c' hc' => ?_, fun D₀ => ?_⟩
          · rcases List.mem_append.1 hc' with h | h
            · exact hb c' (List.mem_cons_of_mem _ h)
            · exact ⟨(hps1 c' h).1, (hps1 c' h).2.1⟩
          · rw [dv_append, dv_rand D₀ σ ps fun c' hc' => (hps1 c' hc').2.2, dv_cons]
            simp [hr]
        · obtain ⟨h1, h2⟩ := ih1 d' hd'
          refine ⟨fun c' hc' => ?_, fun D₀ => ?_⟩
          · rcases List.mem_cons.1 hc' with rfl | h
            · exact hbc
            · exact h1 c' h
          · rw [dv_cons, dv_cons, h2]
      · simp only [Option.map_some, Option.toList_some, List.singleton_append, List.map_cons,
          List.sum_cons, List.map_map, Function.comp_def, rv_cons, rv_append, hr, ite_true]
        rw [dh_mul' A _ _ (val_test A σ c hbc.1 hr) (rv_test A σ cs hcs)]
        rw [show ((dTerms p q cs).map fun d => Comp.val (D ω) σ c * rv (D ω) σ d).sum =
            Comp.val (D ω) σ c * ((dTerms p q cs).map fun d => rv (D ω) σ d).sum by
          rw [List.sum_map_mul_left], ih2 ω, hps2]
        simp only []
        ring
    · have hn := dPieces_none p q c hbc.1 (by simpa using hr)
      rw [dTerms_cons, hn]
      refine ⟨?_, fun ω => ?_⟩
      · intro d hd
        simp only [Option.map_none, Option.toList_none, List.nil_append, List.mem_map] at hd
        obtain ⟨d', hd', rfl⟩ := hd
        obtain ⟨h1, h2⟩ := ih1 d' hd'
        refine ⟨fun c' hc' => ?_, fun D₀ => ?_⟩
        · rcases List.mem_cons.1 hc' with rfl | h
          · exact hbc
          · exact h1 c' h
        · rw [dv_cons, dv_cons, h2]
      · simp only [Option.map_none, Option.toList_none, List.nil_append, List.map_map,
          Function.comp_def, rv_cons, hr, Bool.false_eq_true, ite_false, one_mul]
        exact ih2 ω

end DTerms

section ProdRule

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D)

/-- The product rule over a list whose entries have distinct keys: each factor differentiated
in turn, the others kept. -/
private theorem dh_prod_rule {β : Type*} (a b : ι) (key : β → ℕ) (M : List β)
    (hM : (M.map key).Nodup) (f : β → Ω → ℂ) (hf : ∀ q ∈ M, A.Test (f q)) :
    A.dh a b (fun ω => (M.map fun q => f q ω).prod) = fun ω =>
      (M.map fun q => A.dh a b (f q) ω *
        (M.map fun q' => if key q' = key q then 1 else f q' ω).prod).sum := by
  induction M with
  | nil =>
    funext ω
    simpa using congrFun (A.dh_const a b 1) ω
  | cons q₀ M ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hM
    obtain ⟨hq₀, hM⟩ := hM
    have hf' : ∀ q ∈ M, A.Test (f q) := fun q hq => hf q (List.mem_cons_of_mem _ hq)
    have h1 : (fun ω => ((q₀ :: M).map fun q => f q ω).prod) =
        fun ω => f q₀ ω * (M.map fun q => f q ω).prod := by
      funext ω; simp
    rw [h1, dh_mul' A a b (hf q₀ (List.mem_cons_self ..)) (test_listProd' A M hf'), ih hM hf']
    funext ω
    have hne : ∀ q ∈ M, key q ≠ key q₀ := fun q hq h => hq₀ ⟨q, hq, h⟩
    have h2 : (M.map fun q' => if key q' = key q₀ then 1 else f q' ω) = M.map fun q => f q ω :=
      List.map_congr_left fun q hq => by simp [hne q hq]
    have h3 : ∀ q ∈ M, (if key q₀ = key q then 1 else f q₀ ω) = f q₀ ω := fun q hq => by
      simp [Ne.symm (hne q hq)]
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ite_true, h2, one_mul]
    congr 1
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
    rw [h3 q hq]
    ring

end ProdRule

/-! ## Components by position -/

section Zip

variable {α : Type*}

private theorem zip_snd_nodup (l : List α) : (l.zipIdx.map Prod.snd).Nodup := by
  rw [List.zipIdx_map_snd]
  exact List.nodup_range' ..

private theorem zip_eq_of_snd {l : List α} {p p' : α × ℕ} (hp : p ∈ l.zipIdx)
    (hp' : p' ∈ l.zipIdx) (h : p.2 = p'.2) : p = p' := by
  rw [List.mem_zipIdx_iff_getElem?] at hp hp'
  rw [h, hp'] at hp
  exact Prod.ext (Option.some.inj hp).symm h

private theorem mem_zip_of_get {l : List α} {i : ℕ} {a : α} (h : l[i]? = some a) :
    (a, i) ∈ l.zipIdx :=
  List.mem_zipIdx_iff_getElem?.2 h

private theorem mem_filter_snd {l : List α} {P : α × ℕ → Bool} {p : α × ℕ} (hp : p ∈ l.zipIdx) :
    p.2 ∈ (l.zipIdx.filter P).map Prod.snd ↔ P p = true := by
  constructor
  · intro h
    obtain ⟨q, hq, hqp⟩ := List.mem_map.1 h
    rw [List.mem_filter] at hq
    rw [zip_eq_of_snd hp hq.1 hqp.symm]
    exact hq.2
  · intro h
    exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, h⟩, rfl⟩

private theorem contains_filter_snd {l : List α} {P : α × ℕ → Bool} {p : α × ℕ}
    (hp : p ∈ l.zipIdx) : ((l.zipIdx.filter P).map Prod.snd).contains p.2 = P p := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, mem_filter_snd hp]

private theorem eraseIdx_eq_filter (l : List α) (i : ℕ) :
    l.eraseIdx i = (l.zipIdx.filter fun p => p.2 != i).map Prod.fst := by
  suffices h : ∀ (l : List α) (k i : ℕ),
      ((l.zipIdx k).filter fun p => p.2 != i + k).map Prod.fst = l.eraseIdx i by
    simpa using (h l 0 i).symm
  intro l
  induction l with
  | nil => intro k i; rfl
  | cons a l ih =>
    intro k i
    cases i with
    | zero =>
      simp only [List.zipIdx_cons, Nat.zero_add, List.filter_cons, bne_self_eq_false,
        Bool.false_eq_true, ite_false, List.eraseIdx_cons_zero]
      rw [List.filter_eq_self.2, List.zipIdx_map_fst]
      intro p hp
      have := List.le_snd_of_mem_zipIdx hp
      simp only [bne_iff_ne, ne_eq]
      omega
    | succ i =>
      simp only [List.zipIdx_cons, List.filter_cons, List.eraseIdx_cons_succ]
      have hne : (k != i + 1 + k) = true := by simp
      rw [ite_eq_left hne, List.map_cons]
      congr 1
      rw [← ih (k + 1) i]
      congr 2
      funext p
      congr 1
      omega

private theorem prod_ite_single {M : Type*} [CommMonoid M] (l : List (α × ℕ))
    (hl : (l.map Prod.snd).Nodup) (g : α × ℕ → M) {p : α × ℕ} (hp : p ∈ l) :
    (l.map fun p' => if p'.2 = p.2 then g p' else 1).prod = g p := by
  induction l with
  | nil => simp at hp
  | cons q l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hl
    obtain ⟨hq, hl⟩ := hl
    simp only [List.map_cons, List.prod_cons]
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [ite_eq_left rfl]
      have : (l.map fun p' => if p'.2 = p.2 then g p' else 1) = l.map fun _ => 1 :=
        List.map_congr_left fun p' hp' => ite_eq_right fun h => hq ⟨p', hp', h⟩
      rw [this]
      simp
    · have hne : q.2 ≠ p.2 := fun h => hq ⟨p, hp, h.symm⟩
      rw [ite_eq_right hne, ih hl hp, one_mul]

private theorem prod_single_out {M : Type*} [CommMonoid M] (l : List (α × ℕ))
    (hl : (l.map Prod.snd).Nodup) (g : α × ℕ → M) {p : α × ℕ} (hp : p ∈ l) :
    (l.map g).prod = g p * (l.map fun p' => if p'.2 = p.2 then 1 else g p').prod := by
  rw [← prod_ite_single l hl g hp, ← List.prod_map_mul]
  congr 1
  refine List.map_congr_left fun p' _ => ?_
  split_ifs <;> simp

private theorem sum_filter_snd {M : Type*} [AddCommMonoid M] (l : List (α × ℕ))
    (P : α × ℕ → Bool) (h : ℕ → M) :
    (((l.filter P).map Prod.snd).map h).sum = (l.map fun p => if P p then h p.2 else 0).sum := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    by_cases hq : P q
    · rw [List.filter_cons_of_pos hq]
      simp only [List.map_cons, List.sum_cons, hq, ite_true, ih]
    · rw [List.filter_cons_of_neg hq]
      simp only [List.map_cons, List.sum_cons, hq, Bool.false_eq_true, ite_false, ih, zero_add]

end Zip

section ZipVal

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type*}

private theorem rv_zfilter (D₀ : Data ι) (σ : V → ι) (l : List (Comp V × ℕ))
    (P : Comp V × ℕ → Bool) :
    rv D₀ σ ((l.filter P).map Prod.fst) =
      (l.map fun p => if P p && p.1.kind.isRandom then Comp.val D₀ σ p.1 else 1).prod := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    by_cases hq : P q <;> by_cases hr : q.1.kind.isRandom <;> simp [hq, hr, ih]

private theorem dv_zfilter (D₀ : Data ι) (σ : V → ι) (l : List (Comp V × ℕ))
    (P : Comp V × ℕ → Bool) :
    dv D₀ σ ((l.filter P).map Prod.fst) =
      (l.map fun p => if P p && !p.1.kind.isRandom then Comp.val D₀ σ p.1 else 1).prod := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    by_cases hq : P q <;> by_cases hr : q.1.kind.isRandom <;> simp [hq, hr, ih]

private theorem rv_zip (D₀ : Data ι) (σ : V → ι) (l : List (Comp V)) :
    rv D₀ σ l =
      (l.zipIdx.map fun p => if p.1.kind.isRandom then Comp.val D₀ σ p.1 else 1).prod := by
  have h := rv_zfilter D₀ σ l.zipIdx fun _ => true
  rw [List.filter_true, List.zipIdx_map_fst] at h
  simpa using h

private theorem dv_zip (D₀ : Data ι) (σ : V → ι) (l : List (Comp V)) :
    dv D₀ σ l =
      (l.zipIdx.map fun p => if !p.1.kind.isRandom then Comp.val D₀ σ p.1 else 1).prod := by
  have h := dv_zfilter D₀ σ l.zipIdx fun _ => true
  rw [List.filter_true, List.zipIdx_map_fst] at h
  simpa using h

end ZipVal

/-! ## Values of tracked formal sums, one labelling of the input atoms at a time -/

section Sums

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] (PF : PFamily Ω ι) (D : Ω → Data ι) {k n : ℕ}
  (e : Fin k → ι) (ω : Ω)

/-- The tracked graph with one new atom. -/
private def t1 (cs : List (Comp (Atom k (n + 1)))) (d : Coeff) : Tracked k n :=
  ⟨n + 1, ⟨cs, d⟩, liftA 1⟩

/-- The tracked graph with two new atoms. -/
private def t2 (cs : List (Comp (Atom k (n + 2)))) (d : Coeff) : Tracked k n :=
  ⟨n + 2, ⟨cs, d⟩, liftA 2⟩

/-- The value of a tracked formal sum. -/
private def S (E : TExpansion k n) : ℂ := E.forget.valR PF D e ω

/-- The term of a graph at the labelling `s` of the internal atoms. -/
private def T0 (g : Graph k n) (s : Fin n → ι) : ℂ := g.termR PF D (Sum.elim e s) ω

/-- The terms of a graph with one new atom at the labelling `s` of the internal atoms of the input
graph, summed over the label of the new atom. -/
private def T1 (g : Graph k (n + 1)) (s : Fin n → ι) : ℂ :=
  ∑ α, g.termR PF D (Sum.elim e (Fin.append s ![α])) ω

/-- The terms of a graph with two new atoms at the labelling `s` of the internal atoms of the input
graph, summed over the labels of the new atoms. -/
private def T2 (g : Graph k (n + 2)) (s : Fin n → ι) : ℂ :=
  ∑ α, ∑ β, g.termR PF D (Sum.elim e (Fin.append s ![α, β])) ω

private theorem S_append (E₁ E₂ : TExpansion k n) :
    S PF D e ω (E₁ ++ E₂) = S PF D e ω E₁ + S PF D e ω E₂ := by
  simp [S, TExpansion.forget, Expansion.valR]

private theorem S_nil : S PF D e ω ([] : TExpansion k n) = 0 := by
  simp [S, TExpansion.forget, Expansion.valR]

private theorem S_cons (t : Tracked k n) (E : TExpansion k n) :
    S PF D e ω (t :: E) = t.g.valR PF D e ω + S PF D e ω E := by
  simp [S, TExpansion.forget, Expansion.valR]

private theorem S_ite (b : Prop) [Decidable b] (E : TExpansion k n) :
    S PF D e ω (if b then [] else E) = if b then 0 else S PF D e ω E := by
  by_cases hb : b <;> simp [hb, S_nil]

omit [DecidableEq ι] in
private theorem ite_sum (b : Prop) [Decidable b] (f : (Fin n → ι) → ℂ) :
    (if b then 0 else ∑ s, f s) = ∑ s, if b then 0 else f s := by
  by_cases hb : b <;> simp [hb]

private theorem valR_T0 (g : Graph k n) : g.valR PF D e ω = ∑ s, T0 PF D e ω g s := rfl

private theorem valR_T1 (g : Graph k (n + 1)) : g.valR PF D e ω = ∑ s, T1 PF D e ω g s := by
  rw [valR_split]
  exact Finset.sum_congr rfl fun s _ => sum_fin1 _

private theorem valR_T2 (g : Graph k (n + 2)) : g.valR PF D e ω = ∑ s, T2 PF D e ω g s := by
  rw [valR_split]
  exact Finset.sum_congr rfl fun s _ => sum_fin2 _

omit [DecidableEq ι] in
private theorem list_sum_comm {β : Type*} (l : List β) (f : β → (Fin n → ι) → ℂ) :
    (l.map fun j => ∑ s, f j s).sum = ∑ s, (l.map fun j => f j s).sum := by
  induction l with
  | nil => simp
  | cons j l ih => simp [ih, Finset.sum_add_distrib]

private theorem S_map_t1 {β : Type*} (l : List β) (G : β → List (Comp (Atom k (n + 1))))
    (d : β → Coeff) :
    S PF D e ω (l.map fun j => t1 (G j) (d j)) =
      ∑ s, (l.map fun j => T1 PF D e ω ⟨G j, d j⟩ s).sum := by
  rw [← list_sum_comm]
  simp [S, TExpansion.forget, Expansion.valR, t1, List.map_map, Function.comp_def, valR_T1]

private theorem S_map_t2 {β : Type*} (l : List β) (G : β → List (Comp (Atom k (n + 2))))
    (d : β → Coeff) :
    S PF D e ω (l.map fun j => t2 (G j) (d j)) =
      ∑ s, (l.map fun j => T2 PF D e ω ⟨G j, d j⟩ s).sum := by
  rw [← list_sum_comm]
  simp [S, TExpansion.forget, Expansion.valR, t2, List.map_map, Function.comp_def, valR_T2]

private theorem S_t1 (cs : List (Comp (Atom k (n + 1)))) (d : Coeff) :
    S PF D e ω [t1 cs d] = ∑ s, T1 PF D e ω ⟨cs, d⟩ s := by
  simp [S, TExpansion.forget, Expansion.valR, t1, valR_T1]

private theorem S_t0 (g : Graph k n) (f : Atom k n → Atom k n) :
    S PF D e ω [⟨n, g, f⟩] = ∑ s, T0 PF D e ω g s := by
  simp [S, TExpansion.forget, Expansion.valR, valR_T0]

private theorem S_cons_t0 (g : Graph k n) (f : Atom k n → Atom k n) (E : TExpansion k n) :
    S PF D e ω (⟨n, g, f⟩ :: E) = ∑ s, T0 PF D e ω g s + S PF D e ω E := by
  rw [S_cons]
  rfl

private theorem S_cons_t1 (cs : List (Comp (Atom k (n + 1)))) (d : Coeff) (E : TExpansion k n) :
    S PF D e ω (t1 cs d :: E) = ∑ s, T1 PF D e ω ⟨cs, d⟩ s + S PF D e ω E := by
  rw [S_cons, t1, valR_T1]

private theorem S_cons_t2 (cs : List (Comp (Atom k (n + 2)))) (d : Coeff) (E : TExpansion k n) :
    S PF D e ω (t2 cs d :: E) = ∑ s, T2 PF D e ω ⟨cs, d⟩ s + S PF D e ω E := by
  rw [S_cons, t2, valR_T2]

end Sums

/-! ## Splitting `P_u = 1 - Q_u` -/

/-- A list of components without labels. -/
private def Unl {V : Type*} (cs : List (Comp V)) : Prop := ∀ c ∈ cs, c.label = none

private theorem Unl_append {V : Type*} {cs cs' : List (Comp V)} :
    Unl (cs ++ cs') ↔ Unl cs ∧ Unl cs' := by
  simp [Unl, or_imp, forall_and]

private theorem Unl_mkC {V : Type*} (κ : Kind) (u v : V) (cs : List (Comp V)) :
    Unl (mkC κ u v :: cs) ↔ Unl cs := by
  simp [Unl, mkC]

private theorem Unl_nil {V : Type*} : Unl ([] : List (Comp V)) := by simp [Unl]

private theorem Unl_liftCs {k n : ℕ} (j : ℕ) {cs : List (Comp (Atom k n))} (h : Unl cs) :
    Unl (liftCs j cs) := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  simp [Comp.map, h c' hc']

private theorem Unl_sub {V : Type*} {cs cs' : List (Comp V)} (h : Unl cs) (hs : ∀ c ∈ cs', c ∈ cs) :
    Unl cs' := fun c hc => h c (hs c hc)

section PairLemmas

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k N : ℕ}

/-- An unlabelled graph and its `Q_u` copy with the opposite coefficient: `P_u` of the random
part. -/
private theorem termR_pair (u : Atom k N) (cs ds cs₁ : List (Comp (Atom k N))) (d d' : Coeff)
    (hcs : Unl cs) (hds : Unl ds) (hcs₁ : Unl cs₁) (hr : ∃ c ∈ cs, c.kind.isRandom = true)
    (hd : ∀ z, d'.eval z = -d.eval z)
    (hp : ∀ (D₀ : Data ι) (σ₀ : Atom k N → ι), pv D₀ σ₀ cs₁ = pv D₀ σ₀ cs * pv D₀ σ₀ ds)
    (σ : Atom k N → ι) (ω : Ω) :
    (⟨cs₁, d⟩ : Graph k N).termR PF D σ ω + (⟨labelQs u cs ++ ds, d'⟩ : Graph k N).termR PF D σ ω =
      d.eval (D ω).m * dv (D ω) σ cs * pv (D ω) σ ds *
        PF.P (σ u) (fun ω' => rv (D ω') σ cs) ω := by
  rw [termR_unl (⟨cs₁, d⟩ : Graph k N) hcs₁, termR_Q u cs ds d' hcs hds hr, hd, hp, pv_eq _ _ cs,
    Q_apply']
  ring

/-- A graph with a weight on `u` split as `m + (G_{uu} - m)`, and the `Q_u` copy of the graph
with the weight: `P_u` of the random part with the weight. -/
private theorem termR_triple (u : Atom k N) (ch : Charge) (cs : List (Comp (Atom k N)))
    (d₁ d₂ d₃ : Coeff) (hcs : Unl cs) (h₁ : ∀ z, d₁.eval z = d₂.eval z * ch.apply z)
    (h₃ : ∀ z, d₃.eval z = -d₂.eval z) (σ : Atom k N → ι) (ω : Ω) :
    (⟨cs, d₁⟩ : Graph k N).termR PF D σ ω +
      (⟨cs ++ [mkC (.light ch) u u], d₂⟩ : Graph k N).termR PF D σ ω +
      (⟨labelQs u (cs ++ [mkC (.weight ch) u u]), d₃⟩ : Graph k N).termR PF D σ ω =
      d₂.eval (D ω).m * dv (D ω) σ cs *
        PF.P (σ u) (fun ω' => rv (D ω') σ cs * ch.apply (A.G ω' (σ u) (σ u))) ω := by
  have hw : Unl (cs ++ [mkC (.weight ch) u u]) := Unl_append.2 ⟨hcs, (Unl_mkC _ _ _ _).2 Unl_nil⟩
  have hl : Unl (cs ++ [mkC (.light ch) u u]) := Unl_append.2 ⟨hcs, (Unl_mkC _ _ _ _).2 Unl_nil⟩
  have hQ := termR_Q (PF := PF) (D := D) u (cs ++ [mkC (.weight ch) u u]) [] d₃ hw Unl_nil
    ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩ σ ω
  rw [List.append_nil] at hQ
  rw [termR_unl (⟨cs, d₁⟩ : Graph k N) hcs, termR_unl (⟨_, d₂⟩ : Graph k N) hl, hQ, h₁, h₃,
    Q_apply']
  simp only [pv_append, pv_cons, pv_nil, dv_append, dv_cons, dv_nil, rv_append, rv_cons, rv_nil,
    mul_one, mkC_kind, Kind.isRandom, ite_true, val_light A, val_weight A, m_eq A, pv_eq _ _ cs]
  have hch : ∀ z w : ℂ, ch.apply w = ch.apply z + ch.apply (w - z) := by
    intro z w
    cases ch <;> simp [Charge.apply]
  linear_combination (Coeff.eval (msc A.z) d₂ * dv (D ω) σ cs * rv (D ω) σ cs) *
    (hch (msc A.z) (A.G ω (σ u) (σ u))).symm

end PairLemmas

/-! ## The graphs of the multi-edge expansion, case (i) -/

section OutDefs

variable {k n : ℕ} (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ) (e₁ : Comp (Atom k n))

/-- The indices of the solid edges attached to `x`, in the order of case (i). -/
private def oXIdx : List ℕ :=
  Γ.edgeIdx x .plus true ++ Γ.edgeIdx x .minus true ++ Γ.edgeIdx x .plus false ++
    Γ.edgeIdx x .minus false

/-- The waved edge `s_{xα}`. -/
private def oSx : Comp (Atom k (n + 1)) := mkC (.waved .s) (liftA 1 x) (newA 0)

/-- The solid edge `G_{α y₁}`. -/
private def oGy : Comp (Atom k (n + 1)) := mkC (.G .plus) (newA 0) (liftA 1 e₁.y)

/-- A main term of [I, (3.13)] for the edge `Ḡ_{x y'}` at position `j`: the components other than
`G_{x y₁}` and `Ḡ_{x y'}`, and `s_{xα} G_{α y₁} Ḡ_{α y'}`. -/
private def oBaseM (j : ℕ) : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
    [oSx x, oGy e₁, mkC (.G .minus) (newA 0) (liftA 1 ((Γ.comps.getD j e₁).y))]

/-- A main term of [I, (3.13)] for the edge `G_{w x}` at position `j`: the components other than
`G_{x y₁}` and `G_{w x}`, and `s_{xα} G_{α y₁} G_{w α}`. -/
private def oBaseP (j : ℕ) : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
    [oSx x, oGy e₁, mkC (.G .plus) (liftA 1 ((Γ.comps.getD j e₁).x)) (newA 0)]

/-- The `(k₁ - 1)` term of [I, (3.13)]: the components other than `G_{x y₁}`, and
`s_{xα} G_{xα} G_{α y₁}`. -/
private def oE1 : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (Γ.comps.eraseIdx i₁) ++ [oSx x, mkC (.G .plus) (liftA 1 x) (newA 0), oGy e₁]

/-- The `k₄` term of [I, (3.13)]: the components other than `G_{x y₁}`, and
`s_{xα} Ḡ_{αx} G_{α y₁}`. -/
private def oE2 : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (Γ.comps.eraseIdx i₁) ++ [oSx x, mkC (.G .minus) (newA 0) (liftA 1 x), oGy e₁]

/-- The term `s_{xα} (G_{αα} - m) 𝒢` of [I, (3.13)] and [I, (3.14)]. -/
private def oL3 : List (Comp (Atom k (n + 1))) :=
  liftCs 1 Γ.comps ++ [oSx x, mkC (.light .plus) (newA 0) (newA 0)]

/-- The derivative terms of [I, (3.13)]: the edges at `x` other than `G_{x y₁}`, one graph of
`-∂_{h_{αx}}` of the other components, and `s_{xα} G_{α y₁}`. -/
private def oDs : List (List (Comp (Atom k (n + 1)))) :=
  (dTerms (newA 0) (liftA 1 x) (liftCs 1 (eraseIdxs (oXIdx x Γ) Γ.comps))).map fun d =>
    liftCs 1 (pickIdxs ((oXIdx x Γ).filter (· != i₁)) Γ.comps) ++ d ++ [oSx x, oGy e₁]

/-- The formal sum of `multiEOut`. -/
private def oOut : TExpansion k n :=
  (Γ.edgeIdx x .minus true).map (fun j => t1 (oBaseM x Γ i₁ e₁ j) (cm * cmb * Γ.coeff)) ++
    (Γ.edgeIdx x .plus false).map (fun j => t1 (oBaseP x Γ i₁ e₁ j) (cm * cm * Γ.coeff)) ++
    (Γ.edgeIdx x .minus true).map (fun j => t1 (oBaseM x Γ i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) (cm * Γ.coeff)) ++
    (Γ.edgeIdx x .plus false).map (fun j => t1 (oBaseP x Γ i₁ e₁ j ++
      [mkC (.light .plus) (liftA 1 x) (liftA 1 x)]) (cm * Γ.coeff)) ++
    [t1 (oL3 x Γ) (cm * Γ.coeff)] ++
    (if is₂.isEmpty then [] else [t1 (oE1 x Γ i₁ e₁) ((is₂.length : Coeff) * cm * Γ.coeff)]) ++
    (if (Γ.edgeIdx x .minus false).length = 0 then [] else
      [t1 (oE2 x Γ i₁ e₁) (((Γ.edgeIdx x .minus false).length : Coeff) * cm * Γ.coeff)]) ++
    (oDs x Γ i₁ e₁).map (fun d => t1 d (cm * Γ.coeff)) ++
    [⟨n, ⟨labelQs x Γ.comps, Γ.coeff⟩, id⟩] ++
    (Γ.edgeIdx x .minus true).map (fun j => t1 (labelQs (liftA 1 x) (oBaseM x Γ i₁ e₁ j ++
      [mkC (.weight .minus) (liftA 1 x) (liftA 1 x)])) (-cm * Γ.coeff)) ++
    (Γ.edgeIdx x .plus false).map (fun j => t1 (labelQs (liftA 1 x) (oBaseP x Γ i₁ e₁ j ++
      [mkC (.weight .plus) (liftA 1 x) (liftA 1 x)])) (-cm * Γ.coeff)) ++
    [t1 (labelQs (liftA 1 x) (oL3 x Γ)) (-cm * Γ.coeff)] ++
    (if is₂.isEmpty then [] else
      [t1 (labelQs (liftA 1 x) (oE1 x Γ i₁ e₁)) (-(is₂.length : Coeff) * cm * Γ.coeff)]) ++
    (if (Γ.edgeIdx x .minus false).length = 0 then [] else
      [t1 (labelQs (liftA 1 x) (oE2 x Γ i₁ e₁))
        (-((Γ.edgeIdx x .minus false).length : Coeff) * cm * Γ.coeff)]) ++
    (oDs x Γ i₁ e₁).map (fun d => t1 (labelQs (liftA 1 x) d) (-cm * Γ.coeff))

private theorem multiEOut_some {E : TExpansion k n} (h : multiEOut x Γ = some E) :
    ∃ i₁ is₂ e₁, Γ.edgeIdx x .plus true = i₁ :: is₂ ∧ Γ.comps[i₁]? = some e₁ ∧
      Γ.xdotsAt x (oXIdx x Γ) = true ∧ E = oOut x Γ i₁ is₂ e₁ := by
  unfold multiEOut at h
  split at h
  · exact absurd h (by simp)
  rename_i i₁ is₂ hOP
  split at h
  · exact absurd h (by simp)
  rename_i e₁ hL
  dsimp only at h
  rw [ite_eq_iff] at h
  rcases h with ⟨_, h⟩ | ⟨hX, h⟩
  · exact absurd h (by simp)
  refine ⟨i₁, is₂, e₁, hOP, hL, by simpa [oXIdx] using hX, ?_⟩
  exact (Option.some.inj h).symm

end OutDefs

section LiftVal

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k n j : ℕ} (D₀ : Data ι)

private theorem rv_liftCs (σ : Atom k (n + j) → ι) (cs : List (Comp (Atom k n))) :
    rv D₀ σ (liftCs j cs) = rv D₀ (σ ∘ liftA j) cs := rv_map _ _ _ _

private theorem dv_liftCs (σ : Atom k (n + j) → ι) (cs : List (Comp (Atom k n))) :
    dv D₀ σ (liftCs j cs) = dv D₀ (σ ∘ liftA j) cs := dv_map _ _ _ _

end LiftVal

private theorem fst_mem_of_zip {α : Type*} {l : List α} {p : α × ℕ} (h : p ∈ l.zipIdx) :
    p.1 ∈ l :=
  List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 h)

private theorem mem_eraseIdxs {α : Type*} {is : List ℕ} {l : List α} {a : α}
    (h : a ∈ eraseIdxs is l) : a ∈ l := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  exact fst_mem_of_zip (List.mem_filter.1 hp).1

private theorem mem_pickIdxs {α : Type*} {is : List ℕ} {l : List α} {a : α}
    (h : a ∈ pickIdxs is l) : a ∈ l := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  exact fst_mem_of_zip (List.mem_filter.1 hp).1

private theorem ceval_cm (z : ℂ) : Coeff.eval z cm = z := by simp [Coeff.eval, cm, CVar.eval]

private theorem ceval_cmb (z : ℂ) : Coeff.eval z cmb = star z := by
  simp [Coeff.eval, cmb, CVar.eval]

private theorem ceval_mul (z : ℂ) (p q : Coeff) :
    Coeff.eval z (p * q) = Coeff.eval z p * Coeff.eval z q := by
  simp [Coeff.eval]

private theorem ceval_neg (z : ℂ) (p : Coeff) : Coeff.eval z (-p) = -Coeff.eval z p := by
  simp [Coeff.eval]

private theorem ceval_nat (z : ℂ) (a : ℕ) : Coeff.eval z (a : Coeff) = a := by
  simp [Coeff.eval]

section OutBlocks

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ} (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ)
  (e₁ : Comp (Atom k n)) (e : Fin k → ι) (ω : Ω)

private theorem out_BM (hU : Unl Γ.comps) (j : ℕ) (s : Fin n → ι) :
    T1 PF D e ω ⟨oBaseM x Γ i₁ e₁ j, cm * cmb * Γ.coeff⟩ s +
      T1 PF D e ω ⟨oBaseM x Γ i₁ e₁ j ++ [mkC (.light .minus) (liftA 1 x) (liftA 1 x)],
        cm * Γ.coeff⟩ s +
      T1 PF D e ω ⟨labelQs (liftA 1 x) (oBaseM x Γ i₁ e₁ j ++
        [mkC (.weight .minus) (liftA 1 x) (liftA 1 x)]), -cm * Γ.coeff⟩ s =
    ∑ α, msc A.z * Γ.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] Γ.comps) * (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] Γ.comps) *
        (A.G ω' α (Sum.elim e s e₁.y) * star (A.G ω' α (Sum.elim e s (Γ.comps.getD j e₁).y))) *
        star (A.G ω' (Sum.elim e s x) (Sum.elim e s x))) ω := by
  simp only [T1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hUM : Unl (oBaseM x Γ i₁ e₁ j) := by
    unfold oBaseM oSx oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_eraseIdxs hc),
      by simp [Unl, mkC]⟩
  rw [termR_triple A (liftA 1 x) .minus _ _ _ _ hUM
    (fun z => by simp only [ceval_mul, ceval_cm, ceval_cmb, Charge.apply]; ring)
    (fun z => by simp only [ceval_mul, ceval_neg, ceval_cm]; ring)]
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (oBaseM x Γ i₁ e₁ j) *
      Charge.minus.apply (A.G ω' (Sum.elim e (Fin.append s ![α]) (liftA 1 x))
        (Sum.elim e (Fin.append s ![α]) (liftA 1 x))) =
      rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] Γ.comps) *
        (A.G ω' α (Sum.elim e s e₁.y) * star (A.G ω' α (Sum.elim e s (Γ.comps.getD j e₁).y))) *
        star (A.G ω' (Sum.elim e s x) (Sum.elim e s x)) := by
    intro ω'
    simp only [oBaseM, oSx, oGy, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (oBaseM x Γ i₁ e₁ j) =
      dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] Γ.comps) * (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [oBaseM, oSx, oGy, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  rw [P_congr' hrv, hdv, elim_append_liftA, m_eq A, ceval_mul, ceval_cm]

private theorem out_BP (hU : Unl Γ.comps) (j : ℕ) (s : Fin n → ι) :
    T1 PF D e ω ⟨oBaseP x Γ i₁ e₁ j, cm * cm * Γ.coeff⟩ s +
      T1 PF D e ω ⟨oBaseP x Γ i₁ e₁ j ++ [mkC (.light .plus) (liftA 1 x) (liftA 1 x)],
        cm * Γ.coeff⟩ s +
      T1 PF D e ω ⟨labelQs (liftA 1 x) (oBaseP x Γ i₁ e₁ j ++
        [mkC (.weight .plus) (liftA 1 x) (liftA 1 x)]), -cm * Γ.coeff⟩ s =
    ∑ α, msc A.z * Γ.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] Γ.comps) * (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] Γ.comps) *
        (A.G ω' α (Sum.elim e s e₁.y) * A.G ω' (Sum.elim e s (Γ.comps.getD j e₁).x) α) *
        A.G ω' (Sum.elim e s x) (Sum.elim e s x)) ω := by
  simp only [T1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hUM : Unl (oBaseP x Γ i₁ e₁ j) := by
    unfold oBaseP oSx oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_eraseIdxs hc),
      by simp [Unl, mkC]⟩
  rw [termR_triple A (liftA 1 x) .plus _ _ _ _ hUM
    (fun z => by simp only [ceval_mul, ceval_cm, Charge.apply]; ring)
    (fun z => by simp only [ceval_mul, ceval_neg, ceval_cm]; ring)]
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (oBaseP x Γ i₁ e₁ j) *
      Charge.plus.apply (A.G ω' (Sum.elim e (Fin.append s ![α]) (liftA 1 x))
        (Sum.elim e (Fin.append s ![α]) (liftA 1 x))) =
      rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] Γ.comps) *
        (A.G ω' α (Sum.elim e s e₁.y) * A.G ω' (Sum.elim e s (Γ.comps.getD j e₁).x) α) *
        A.G ω' (Sum.elim e s x) (Sum.elim e s x) := by
    intro ω'
    simp only [oBaseP, oSx, oGy, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (oBaseP x Γ i₁ e₁ j) =
      dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] Γ.comps) * (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [oBaseP, oSx, oGy, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  rw [P_congr' hrv, hdv, elim_append_liftA, m_eq A, ceval_mul, ceval_cm]

private theorem termR_pair0 {N : ℕ} (u : Atom k N) (cs : List (Comp (Atom k N))) (d d' : Coeff)
    (hcs : Unl cs) (hr : ∃ c ∈ cs, c.kind.isRandom = true) (hd : ∀ z, d'.eval z = -d.eval z)
    (σ : Atom k N → ι) (ω : Ω) :
    (⟨cs, d⟩ : Graph k N).termR PF D σ ω + (⟨labelQs u cs, d'⟩ : Graph k N).termR PF D σ ω =
      d.eval (D ω).m * dv (D ω) σ cs * PF.P (σ u) (fun ω' => rv (D ω') σ cs) ω := by
  have h := termR_pair (PF := PF) (D := D) u cs [] cs d d' hcs Unl_nil hcs hr hd
    (fun D₀ σ₀ => by simp) σ ω
  rw [List.append_nil] at h
  rw [h]
  simp

private theorem out_BL (hU : Unl Γ.comps) (s : Fin n → ι) :
    T1 PF D e ω ⟨oL3 x Γ, cm * Γ.coeff⟩ s +
      T1 PF D e ω ⟨labelQs (liftA 1 x) (oL3 x Γ), -cm * Γ.coeff⟩ s =
    ∑ α, msc A.z * Γ.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) Γ.comps * (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) Γ.comps *
        (A.G ω' α α - msc A.z)) ω := by
  simp only [T1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hU3 : Unl (oL3 x Γ) := by
    unfold oL3 oSx
    exact Unl_append.2 ⟨Unl_liftCs 1 hU, by simp [Unl, mkC]⟩
  rw [termR_pair0 (liftA 1 x) _ _ _ hU3
    ⟨mkC (.light .plus) (newA 0) (newA 0), List.mem_append_right _ (by simp), rfl⟩
    (fun z => by simp only [ceval_mul, ceval_neg, ceval_cm]; ring)]
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (oL3 x Γ) =
      rv (D ω') (Sum.elim e s) Γ.comps * (A.G ω' α α - msc A.z) := by
    intro ω'
    simp only [oL3, oSx, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_light A,
      elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (oL3 x Γ) =
      dv (D ω) (Sum.elim e s) Γ.comps * (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [oL3, oSx, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  rw [P_congr' hrv, hdv, elim_append_liftA, m_eq A, ceval_mul, ceval_cm]

private theorem out_BE1 (hU : Unl Γ.comps) (b : Prop) [Decidable b] (a : ℕ) (hb : b → a = 0)
    (s : Fin n → ι) :
    (if b then 0 else T1 PF D e ω ⟨oE1 x Γ i₁ e₁, (a : Coeff) * cm * Γ.coeff⟩ s) +
      (if b then 0 else
        T1 PF D e ω ⟨labelQs (liftA 1 x) (oE1 x Γ i₁ e₁), -(a : Coeff) * cm * Γ.coeff⟩ s) =
    ∑ α, (a : ℂ) * msc A.z * Γ.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (Γ.comps.eraseIdx i₁) * (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) (Γ.comps.eraseIdx i₁) *
        (A.G ω' (Sum.elim e s x) α * A.G ω' α (Sum.elim e s e₁.y))) ω := by
  by_cases hb' : b
  · simp [hb', hb hb']
  simp only [hb', ite_false, T1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hU3 : Unl (oE1 x Γ i₁ e₁) := by
    unfold oE1 oSx oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => List.mem_of_mem_eraseIdx hc),
      by simp [Unl, mkC]⟩
  rw [termR_pair0 (liftA 1 x) _ _ _ hU3
    ⟨oGy e₁, List.mem_append_right _ (by simp), rfl⟩
    (fun z => by simp only [ceval_mul, ceval_neg, ceval_cm]; ring)]
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (oE1 x Γ i₁ e₁) =
      rv (D ω') (Sum.elim e s) (Γ.comps.eraseIdx i₁) *
        (A.G ω' (Sum.elim e s x) α * A.G ω' α (Sum.elim e s e₁.y)) := by
    intro ω'
    simp only [oE1, oSx, oGy, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (oE1 x Γ i₁ e₁) =
      dv (D ω) (Sum.elim e s) (Γ.comps.eraseIdx i₁) * (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [oE1, oSx, oGy, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  rw [P_congr' hrv, hdv, elim_append_liftA, m_eq A, ceval_mul, ceval_mul, ceval_cm, ceval_nat]

private theorem out_BE2 (hU : Unl Γ.comps) (b : Prop) [Decidable b] (a : ℕ) (hb : b → a = 0)
    (s : Fin n → ι) :
    (if b then 0 else T1 PF D e ω ⟨oE2 x Γ i₁ e₁, (a : Coeff) * cm * Γ.coeff⟩ s) +
      (if b then 0 else
        T1 PF D e ω ⟨labelQs (liftA 1 x) (oE2 x Γ i₁ e₁), -(a : Coeff) * cm * Γ.coeff⟩ s) =
    ∑ α, (a : ℂ) * msc A.z * Γ.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (Γ.comps.eraseIdx i₁) * (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) (Γ.comps.eraseIdx i₁) *
        (star (A.G ω' α (Sum.elim e s x)) * A.G ω' α (Sum.elim e s e₁.y))) ω := by
  by_cases hb' : b
  · simp [hb', hb hb']
  simp only [hb', ite_false, T1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hU3 : Unl (oE2 x Γ i₁ e₁) := by
    unfold oE2 oSx oGy
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => List.mem_of_mem_eraseIdx hc),
      by simp [Unl, mkC]⟩
  rw [termR_pair0 (liftA 1 x) _ _ _ hU3
    ⟨oGy e₁, List.mem_append_right _ (by simp), rfl⟩
    (fun z => by simp only [ceval_mul, ceval_neg, ceval_cm]; ring)]
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (oE2 x Γ i₁ e₁) =
      rv (D ω') (Sum.elim e s) (Γ.comps.eraseIdx i₁) *
        (star (A.G ω' α (Sum.elim e s x)) * A.G ω' α (Sum.elim e s e₁.y)) := by
    intro ω'
    simp only [oE2, oSx, oGy, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (oE2 x Γ i₁ e₁) =
      dv (D ω) (Sum.elim e s) (Γ.comps.eraseIdx i₁) * (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [oE2, oSx, oGy, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  rw [P_congr' hrv, hdv, elim_append_liftA, m_eq A, ceval_mul, ceval_mul, ceval_cm, ceval_nat]

private theorem plain_Unl {k n : ℕ} {cs : List (Comp (Atom k n))}
    (h : ∀ c ∈ cs, c.isPlainB = true) : Unl cs := fun c hc => (basB_of_plain (h c hc)).2

private theorem plain_bas_lift {k n : ℕ} {cs : List (Comp (Atom k n))}
    (h : ∀ c ∈ cs, c.isPlainB = true) (j : ℕ) :
    ∀ c ∈ liftCs j cs, basB c = true ∧ c.label = none := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  obtain ⟨h1, h2⟩ := basB_of_plain (h c' hc')
  exact ⟨by rw [basB_map]; exact h1, by simp [Comp.map, h2]⟩

private theorem out_BD (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) (s : Fin n → ι) :
    ((oDs x Γ i₁ e₁).map fun d => T1 PF D e ω ⟨d, cm * Γ.coeff⟩ s).sum +
      ((oDs x Γ i₁ e₁).map fun d =>
        T1 PF D e ω ⟨labelQs (liftA 1 x) d, -cm * Γ.coeff⟩ s).sum =
    ((oDs x Γ i₁ e₁).map fun d => ∑ α, msc A.z * Γ.coeff.eval (msc A.z) *
      dv (D ω) (Sum.elim e (Fin.append s ![α])) d *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e (Fin.append s ![α])) d) ω).sum := by
  rw [← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun d hd => ?_)
  simp only [T1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
  have hpl' : ∀ c ∈ eraseIdxs (oXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  have hd'U := ((dTerms_spec A (Sum.elim e (Fin.append s ![α])) (newA 0) (liftA 1 x) _
    (plain_bas_lift hpl' 1)).1 d' hd').1
  have hU3 : Unl (liftCs 1 (pickIdxs ((oXIdx x Γ).filter (· != i₁)) Γ.comps) ++ d' ++
      [oSx x, oGy e₁]) := by
    refine Unl_append.2 ⟨Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub (plain_Unl hpl) fun c hc =>
      mem_pickIdxs hc), fun c hc => (hd'U c hc).2⟩, by simp [Unl, oSx, oGy, mkC]⟩
  rw [termR_pair0 (liftA 1 x) _ _ _ hU3
    ⟨oGy e₁, List.mem_append_right _ (by simp), rfl⟩
    (fun z => by simp only [ceval_mul, ceval_neg, ceval_cm]; ring),
    elim_append_liftA, m_eq A, ceval_mul, ceval_cm]

private theorem out_BQ (hU : Unl Γ.comps) (hr : ∃ c ∈ Γ.comps, c.kind.isRandom = true)
    (s : Fin n → ι) :
    T0 PF D e ω ⟨labelQs x Γ.comps, Γ.coeff⟩ s =
      Γ.coeff.eval (msc A.z) * dv (D ω) (Sum.elim e s) Γ.comps *
        PF.op .Q (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) Γ.comps) ω := by
  have h := termR_Q (PF := PF) (D := D) x Γ.comps [] Γ.coeff hU Unl_nil hr (Sum.elim e s) ω
  rw [List.append_nil] at h
  rw [T0, h, m_eq A]
  simp

private theorem T0_self (hU : Unl Γ.comps) (s : Fin n → ι) :
    T0 PF D e ω Γ s = Γ.coeff.eval (msc A.z) * dv (D ω) (Sum.elim e s) Γ.comps *
      rv (D ω) (Sum.elim e s) Γ.comps := by
  rw [T0, termR_unl Γ hU, m_eq A, pv_eq]
  ring

end OutBlocks

/-! ## Solid edges at `x` by position -/

section EdgePos

variable {k n : ℕ} (x : Atom k n)

/-- The filter of `Graph.edgeIdx`. -/
private def ep (ch : Charge) (out : Bool) : Comp (Atom k n) × ℕ → Bool := fun p =>
  p.1.kind == .G ch && (if out then p.1.x == x && p.1.y != x else p.1.y == x && p.1.x != x)

private theorem edgeIdx_eq (Γ : Graph k n) (ch : Charge) (out : Bool) :
    Γ.edgeIdx x ch out = (Γ.comps.zipIdx.filter (ep x ch out)).map Prod.snd := rfl

/-- The component at a position is a solid edge attached to `x` (self-loops excluded). -/
private def cX (p : Comp (Atom k n) × ℕ) : Bool :=
  ep x .plus true p || ep x .minus true p || ep x .plus false p || ep x .minus false p

private theorem ep_spec {ch : Charge} {out : Bool} {p : Comp (Atom k n) × ℕ}
    (h : ep x ch out p = true) :
    p.1.kind = .G ch ∧ (out = true → p.1.x = x ∧ p.1.y ≠ x) ∧
      (out = false → p.1.y = x ∧ p.1.x ≠ x) := by
  unfold ep at h
  cases out <;> simp_all

private theorem cX_random {p : Comp (Atom k n) × ℕ} (h : cX x p = true) :
    p.1.kind.isRandom = true := by
  unfold cX at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h <;> rw [(ep_spec x h).1] <;> rfl

private theorem cX_of_ep {ch : Charge} {out : Bool} {p : Comp (Atom k n) × ℕ}
    (h : ep x ch out p = true) : cX x p = true := by
  unfold cX
  cases ch <;> cases out <;> simp [h]

/-- At most one of the four filters holds. -/
private theorem ep_excl {p : Comp (Atom k n) × ℕ} {ch ch' : Charge} {out out' : Bool}
    (h : ep x ch out p = true) (h' : ep x ch' out' p = true) : ch = ch' ∧ out = out' := by
  obtain ⟨k1, o1, i1⟩ := ep_spec x h
  obtain ⟨k2, o2, i2⟩ := ep_spec x h'
  rw [k1] at k2
  refine ⟨by injection k2, ?_⟩
  cases out <;> cases out'
  · rfl
  · exact absurd (o2 rfl).1 (i1 rfl).2
  · exact absurd (o1 rfl).1 (i2 rfl).2
  · rfl

private theorem contains_oXIdx (Γ : Graph k n) {p : Comp (Atom k n) × ℕ}
    (hp : p ∈ Γ.comps.zipIdx) : (oXIdx x Γ).contains p.2 = cX x p := by
  simp only [oXIdx, edgeIdx_eq, List.contains_append, contains_filter_snd hp, cX]

end EdgePos

/-! ## Products over the components, with the solid edges at `x` singled out -/

section EdgeProd

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k n : ℕ} (cP : Comp (Atom k n) × ℕ → Bool)
  (Γ : Graph k n) (i₁ : ℕ) (σ : Atom k n → ι)

/-- The factor at a position of the edges selected by `cP`, the edge at `i₁` excepted. -/
private def kx (D₀ : Data ι) (p : Comp (Atom k n) × ℕ) : ℂ :=
  if cP p && p.2 != i₁ then Comp.val D₀ σ p.1 else 1

/-- The product of the edges selected by `cP`, the edge at `i₁` excepted. -/
private def Kx (D₀ : Data ι) : ℂ := (Γ.comps.zipIdx.map (kx cP i₁ σ D₀)).prod

/-- The product of the edges selected by `cP`, the edges at `i₁` and `j` excepted. -/
private def Kxq (D₀ : Data ι) (j : ℕ) : ℂ :=
  (Γ.comps.zipIdx.map fun p => if p.2 = j then 1 else kx cP i₁ σ D₀ p).prod

/-- `Kx` with the factor at `q` singled out. -/
private theorem Kx_single (D₀ : Data ι) {q : Comp (Atom k n) × ℕ} (hq : q ∈ Γ.comps.zipIdx) :
    Kx cP Γ i₁ σ D₀ = kx cP i₁ σ D₀ q * Kxq cP Γ i₁ σ D₀ q.2 :=
  prod_single_out _ (zip_snd_nodup _) _ hq

variable {cP Γ i₁} {xI : List ℕ} {e₁ : Comp (Atom k n)}
  (hxI : ∀ p ∈ Γ.comps.zipIdx, xI.contains p.2 = cP p)
  (hcR : ∀ p, cP p = true → p.1.kind.isRandom = true)
  (he : (e₁, i₁) ∈ Γ.comps.zipIdx) (hce : cP (e₁, i₁) = true)

include hxI hcR he hce in
private theorem gR1 (D₀ : Data ι) :
    rv D₀ σ Γ.comps = Comp.val D₀ σ e₁ * (Kx cP Γ i₁ σ D₀ * rv D₀ σ (eraseIdxs xI Γ.comps)) := by
  rw [rv_zip, Kx, eraseIdxs, rv_zfilter,
    ← prod_ite_single _ (zip_snd_nodup _) (fun p => Comp.val D₀ σ p.1) he,
    ← List.prod_map_mul, ← List.prod_map_mul]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  rw [hxI p hp, kx]
  by_cases h1 : p.2 = i₁
  · obtain rfl := zip_eq_of_snd hp he h1
    simp [hce, hcR _ hce]
  · by_cases hc : cP p = true
    · simp [hc, hcR _ hc, h1]
    · simp [hc, h1]

include hxI hcR he hce in
private theorem gR2 (D₀ : Data ι) :
    rv D₀ σ (Γ.comps.eraseIdx i₁) = Kx cP Γ i₁ σ D₀ * rv D₀ σ (eraseIdxs xI Γ.comps) := by
  rw [eraseIdx_eq_filter, rv_zfilter, Kx, eraseIdxs, rv_zfilter, ← List.prod_map_mul]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  rw [hxI p hp, kx]
  by_cases h1 : p.2 = i₁
  · obtain rfl := zip_eq_of_snd hp he h1
    simp [hce]
  · by_cases hc : cP p = true
    · simp [hc, hcR _ hc, h1]
    · simp [hc, h1]

include hxI hcR he hce in
private theorem gR3 (D₀ : Data ι) {q : Comp (Atom k n) × ℕ} (hq : q ∈ Γ.comps.zipIdx)
    (hqc : cP q = true) :
    rv D₀ σ (eraseIdxs [i₁, q.2] Γ.comps) =
      Kxq cP Γ i₁ σ D₀ q.2 * rv D₀ σ (eraseIdxs xI Γ.comps) := by
  rw [eraseIdxs, rv_zfilter, Kxq, eraseIdxs, rv_zfilter, ← List.prod_map_mul]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  rw [hxI p hp, kx]
  by_cases h2 : p.2 = q.2
  · obtain rfl := zip_eq_of_snd hp hq h2
    simp [hqc]
  by_cases h1 : p.2 = i₁
  · obtain rfl := zip_eq_of_snd hp he h1
    simp [hce]
  · by_cases hc : cP p = true
    · simp [hc, hcR _ hc, h1, h2]
    · simp [hc, h1, h2]

include hxI hcR in
private theorem gR4 (D₀ : Data ι) :
    rv D₀ σ (pickIdxs (xI.filter (· != i₁)) Γ.comps) = Kx cP Γ i₁ σ D₀ := by
  rw [pickIdxs, rv_zfilter, Kx]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  have hcont : (xI.filter (· != i₁)).contains p.2 = (cP p && p.2 != i₁) := by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.mem_filter, ← List.contains_iff_mem,
      hxI p hp]
    simp
  rw [hcont, kx]
  by_cases hc : cP p = true
  · simp [hc, hcR _ hc]
  · simp [hc]

include hcR he hce in
private theorem gD1 (D₀ : Data ι) : dv D₀ σ (Γ.comps.eraseIdx i₁) = dv D₀ σ Γ.comps := by
  rw [eraseIdx_eq_filter, dv_zfilter, dv_zip]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  by_cases h1 : p.2 = i₁
  · obtain rfl := zip_eq_of_snd hp he h1
    simp [hcR _ hce]
  · simp [h1]

include hcR he hce in
private theorem gD3 (D₀ : Data ι) {q : Comp (Atom k n) × ℕ} (hq : q ∈ Γ.comps.zipIdx)
    (hqc : cP q = true) : dv D₀ σ (eraseIdxs [i₁, q.2] Γ.comps) = dv D₀ σ Γ.comps := by
  rw [eraseIdxs, dv_zfilter, dv_zip]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  by_cases h2 : p.2 = q.2
  · obtain rfl := zip_eq_of_snd hp hq h2
    simp [hcR _ hqc]
  by_cases h1 : p.2 = i₁
  · obtain rfl := zip_eq_of_snd hp he h1
    simp [hcR _ hce]
  · simp [h1, h2]

include hxI hcR in
private theorem gD4 (D₀ : Data ι) :
    dv D₀ σ (eraseIdxs xI Γ.comps) = dv D₀ σ Γ.comps := by
  rw [eraseIdxs, dv_zfilter, dv_zip]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  rw [hxI p hp]
  by_cases hc : cP p = true
  · simp [hc, hcR _ hc]
  · simp [hc]

include hxI hcR in
private theorem gD5 (D₀ : Data ι) :
    dv D₀ σ (pickIdxs (xI.filter (· != i₁)) Γ.comps) = 1 := by
  rw [pickIdxs, dv_zfilter]
  refine List.prod_eq_one fun a ha => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
  have hcont : (xI.filter (· != i₁)).contains p.2 = (cP p && p.2 != i₁) := by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.mem_filter, ← List.contains_iff_mem,
      hxI p hp]
    simp
  rw [hcont]
  by_cases hc : cP p = true
  · simp [hc, hcR _ hc]
  · simp [hc]

end EdgeProd

/-! ## Case (i): the products over the components -/

section OutProd

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k n : ℕ} {x : Atom k n} {Γ : Graph k n}
  {i₁ : ℕ} (σ : Atom k n → ι) {is₂ : List ℕ} {e₁ : Comp (Atom k n)}

omit [Fintype ι] [DecidableEq ι] in
private theorem out_hxI : ∀ p ∈ Γ.comps.zipIdx, (oXIdx x Γ).contains p.2 = cX x p :=
  fun _ hp => contains_oXIdx x Γ hp

variable (hOP : Γ.edgeIdx x .plus true = i₁ :: is₂) (hL : Γ.comps[i₁]? = some e₁)
include hOP hL

omit [Fintype ι] [DecidableEq ι] hOP in
private theorem e₁_mem : (e₁, i₁) ∈ Γ.comps.zipIdx := mem_zip_of_get hL

omit [Fintype ι] [DecidableEq ι] in
private theorem e₁_ep : ep x .plus true (e₁, i₁) = true := by
  have h : i₁ ∈ Γ.edgeIdx x .plus true := by rw [hOP]; exact List.mem_cons_self ..
  rw [edgeIdx_eq] at h
  exact (mem_filter_snd (e₁_mem hL)).1 h

private theorem out_R1 (D₀ : Data ι) :
    rv D₀ σ Γ.comps = Comp.val D₀ σ e₁ *
      (Kx (cX x) Γ i₁ σ D₀ * rv D₀ σ (eraseIdxs (oXIdx x Γ) Γ.comps)) :=
  gR1 σ out_hxI (fun _ h => cX_random x h) (e₁_mem hL) (cX_of_ep x (e₁_ep hOP hL)) D₀

private theorem out_R2 (D₀ : Data ι) :
    rv D₀ σ (Γ.comps.eraseIdx i₁) =
      Kx (cX x) Γ i₁ σ D₀ * rv D₀ σ (eraseIdxs (oXIdx x Γ) Γ.comps) :=
  gR2 σ out_hxI (fun _ h => cX_random x h) (e₁_mem hL) (cX_of_ep x (e₁_ep hOP hL)) D₀

private theorem out_R3 (D₀ : Data ι) {q : Comp (Atom k n) × ℕ} (hq : q ∈ Γ.comps.zipIdx)
    (hqc : cX x q = true) :
    rv D₀ σ (eraseIdxs [i₁, q.2] Γ.comps) =
      Kxq (cX x) Γ i₁ σ D₀ q.2 * rv D₀ σ (eraseIdxs (oXIdx x Γ) Γ.comps) :=
  gR3 σ out_hxI (fun _ h => cX_random x h) (e₁_mem hL) (cX_of_ep x (e₁_ep hOP hL)) D₀ hq hqc

private theorem out_D1 (D₀ : Data ι) : dv D₀ σ (Γ.comps.eraseIdx i₁) = dv D₀ σ Γ.comps :=
  gD1 σ (fun _ h => cX_random x h) (e₁_mem hL) (cX_of_ep x (e₁_ep hOP hL)) D₀

private theorem out_D3 (D₀ : Data ι) {q : Comp (Atom k n) × ℕ} (hq : q ∈ Γ.comps.zipIdx)
    (hqc : cX x q = true) : dv D₀ σ (eraseIdxs [i₁, q.2] Γ.comps) = dv D₀ σ Γ.comps :=
  gD3 σ (fun _ h => cX_random x h) (e₁_mem hL) (cX_of_ep x (e₁_ep hOP hL)) D₀ hq hqc

omit hOP hL in
private theorem out_R4 (D₀ : Data ι) :
    rv D₀ σ (pickIdxs ((oXIdx x Γ).filter (· != i₁)) Γ.comps) = Kx (cX x) Γ i₁ σ D₀ :=
  gR4 σ out_hxI (fun _ h => cX_random x h) D₀

omit hOP hL in
private theorem out_D4 (D₀ : Data ι) :
    dv D₀ σ (eraseIdxs (oXIdx x Γ) Γ.comps) = dv D₀ σ Γ.comps :=
  gD4 σ out_hxI (fun _ h => cX_random x h) D₀

omit hOP hL in
private theorem out_D5 (D₀ : Data ι) :
    dv D₀ σ (pickIdxs ((oXIdx x Γ).filter (· != i₁)) Γ.comps) = 1 :=
  gD5 σ out_hxI (fun _ h => cX_random x h) D₀

end OutProd

/-! ## Case (i): `-∂_{h_{αx}}` of the edges at `x` -/

section OutDeriv

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ} {x : Atom k n} {Γ : Graph k n} (σ : Atom k n → ι)

private theorem getD_of_zip {p : Comp (Atom k n) × ℕ} (hp : p ∈ Γ.comps.zipIdx)
    (d : Comp (Atom k n)) : Γ.comps.getD p.2 d = p.1 := by
  rw [List.getD_eq_getElem?_getD, List.mem_zipIdx_iff_getElem?.1 hp]
  rfl

/-- The factor of a solid edge without minor. -/
private theorem val_edge {c : Comp (Atom k n)} (hc : c.isPlainB = true) {ch : Charge}
    (hk : c.kind = .G ch) (ω : Ω) :
    Comp.val (D ω) σ c = ch.apply (A.G ω (σ c.x) (σ c.y)) := by
  rcases c with ⟨κ, a, b, mi, l⟩
  simp only [Comp.isPlainB, Bool.and_eq_true, List.isEmpty_iff] at hc
  obtain ⟨⟨rfl, _⟩, _⟩ := hc
  simp only at hk
  subst hk
  exact val_G A σ ω ch a b

private theorem fun_edge {c : Comp (Atom k n)} (hc : c.isPlainB = true) {ch : Charge}
    (hk : c.kind = .G ch) :
    (fun ω => Comp.val (D ω) σ c) = fun ω => ch.apply (A.G ω (σ c.x) (σ c.y)) :=
  funext fun ω => val_edge A σ hc hk ω

private theorem dh_OP {p : Comp (Atom k n) × ℕ} (hc : p.1.isPlainB = true)
    (h : ep x .plus true p = true) (β : ι) :
    A.dh β (σ x) (fun ω => Comp.val (D ω) σ p.1) =
      fun ω => -(A.G ω (σ x) β * Comp.val (D ω) σ p.1) := by
  obtain ⟨hk, ho, -⟩ := ep_spec x h
  rw [fun_edge A σ hc hk]
  simp only [Charge.apply, dh_G', (ho rfl).1, val_edge A σ hc hk]

private theorem dh_OM {p : Comp (Atom k n) × ℕ} (hc : p.1.isPlainB = true)
    (h : ep x .minus true p = true) (β : ι) :
    A.dh β (σ x) (fun ω => Comp.val (D ω) σ p.1) =
      fun ω => -(star (A.G ω (σ x) (σ x)) * star (A.G ω β (σ p.1.y))) := by
  obtain ⟨hk, ho, -⟩ := ep_spec x h
  rw [fun_edge A σ hc hk]
  simp only [Charge.apply, dh_starG', (ho rfl).1]

private theorem dh_IP {p : Comp (Atom k n) × ℕ} (hc : p.1.isPlainB = true)
    (h : ep x .plus false p = true) (β : ι) :
    A.dh β (σ x) (fun ω => Comp.val (D ω) σ p.1) =
      fun ω => -(A.G ω (σ p.1.x) β * A.G ω (σ x) (σ x)) := by
  obtain ⟨hk, -, hi⟩ := ep_spec x h
  rw [fun_edge A σ hc hk]
  simp only [Charge.apply, dh_G', (hi rfl).1]

private theorem dh_IM {p : Comp (Atom k n) × ℕ} (hc : p.1.isPlainB = true)
    (h : ep x .minus false p = true) (β : ι) :
    A.dh β (σ x) (fun ω => Comp.val (D ω) σ p.1) =
      fun ω => -(Comp.val (D ω) σ p.1 * star (A.G ω β (σ x))) := by
  obtain ⟨hk, -, hi⟩ := ep_spec x h
  rw [fun_edge A σ hc hk]
  simp only [Charge.apply, dh_starG', (hi rfl).1, val_edge A σ hc hk]

private theorem kx_test (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true)
    {cP : Comp (Atom k n) × ℕ → Bool} (hcR : ∀ p, cP p = true → p.1.kind.isRandom = true)
    (i₁ : ℕ) {p : Comp (Atom k n) × ℕ} (hp : p ∈ Γ.comps.zipIdx) :
    A.Test fun ω => kx cP i₁ σ (D ω) p := by
  unfold kx
  by_cases hb : (cP p && p.2 != i₁) = true
  · simp only [hb, ite_true]
    have hc := Bool.and_eq_true_iff.1 hb
    exact val_test A σ p.1 (basB_of_plain (hpl _ (fst_mem_of_zip hp))).1 (hcR _ hc.1)
  · simp only [hb]
    exact test_const' A 1

private theorem dh_kx (cP : Comp (Atom k n) × ℕ → Bool) (i₁ : ℕ) (p : Comp (Atom k n) × ℕ)
    (a b : ι) :
    A.dh a b (fun ω => kx cP i₁ σ (D ω) p) =
      if (cP p && p.2 != i₁) = true then A.dh a b (fun ω => Comp.val (D ω) σ p.1) else 0 := by
  unfold kx
  by_cases hb : (cP p && p.2 != i₁) = true
  · simp only [hb, ite_true]
  · simp only [hb, Bool.false_eq_true, ite_false]
    exact A.dh_const a b 1

private theorem ep_false {p : Comp (Atom k n) × ℕ} {ch ch' : Charge} {out out' : Bool}
    (h : ep x ch out p = true) (hne : ¬ (ch = ch' ∧ out = out')) : ep x ch' out' p = false := by
  by_contra h'
  exact hne (ep_excl x h (by simpa using h'))

/-- The term of `-∂_{h_{βx}}` at one position, times the other factors, sorted into the four
families of [I, (3.13)]. -/
private theorem out_PP (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hOP : Γ.edgeIdx x .plus true = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) {p : Comp (Atom k n) × ℕ} (hp : p ∈ Γ.comps.zipIdx)
    (β : ι) (ω : Ω) :
    -(A.dh β (σ x) (fun ω => kx (cX x) i₁ σ (D ω) p) ω) * Kxq (cX x) Γ i₁ σ (D ω) p.2 *
        rv (D ω) σ (eraseIdxs (oXIdx x Γ) Γ.comps) * A.G ω β (σ e₁.y) =
      (if ep x .minus true p = true then rv (D ω) σ (eraseIdxs [i₁, p.2] Γ.comps) *
          (A.G ω β (σ e₁.y) * star (A.G ω β (σ (Γ.comps.getD p.2 e₁).y))) *
          star (A.G ω (σ x) (σ x)) else 0) +
      (if ep x .plus false p = true then rv (D ω) σ (eraseIdxs [i₁, p.2] Γ.comps) *
          (A.G ω β (σ e₁.y) * A.G ω (σ (Γ.comps.getD p.2 e₁).x) β) *
          A.G ω (σ x) (σ x) else 0) +
      (if (ep x .plus true p && p.2 != i₁) = true then rv (D ω) σ (Γ.comps.eraseIdx i₁) *
          (A.G ω (σ x) β * A.G ω β (σ e₁.y)) else 0) +
      (if ep x .minus false p = true then rv (D ω) σ (Γ.comps.eraseIdx i₁) *
          (star (A.G ω β (σ x)) * A.G ω β (σ e₁.y)) else 0) := by
  have hplp := hpl _ (fst_mem_of_zip hp)
  rw [dh_kx A σ (cX x) i₁ p]
  by_cases hb : (cX x p && p.2 != i₁) = true
  · rw [ite_eq_left hb]
    obtain ⟨hc, hne⟩ := Bool.and_eq_true_iff.1 hb
    have hne' : p.2 ≠ i₁ := by simpa using hne
    have hK := Kx_single (cX x) Γ i₁ σ (D ω) hp
    rw [kx, ite_eq_left hb] at hK
    have hgd := getD_of_zip hp e₁
    simp only [cX, Bool.or_eq_true] at hc
    rcases hc with ((h | h) | h) | h
    · rw [dh_OP A σ hplp h, out_R2 σ hOP hL, hK,
        ep_false h (ch' := .minus) (out' := true) (by simp),
        ep_false h (ch' := .plus) (out' := false) (by simp),
        ep_false h (ch' := .minus) (out' := false) (by simp)]
      simp only [h, hne, Bool.and_self, ite_true, Bool.false_eq_true, ite_false]
      ring
    · rw [dh_OM A σ hplp h, out_R3 σ hOP hL (D ω) hp (cX_of_ep x h), hgd,
        ep_false h (ch' := .plus) (out' := false) (by simp),
        ep_false h (ch' := .plus) (out' := true) (by simp),
        ep_false h (ch' := .minus) (out' := false) (by simp)]
      simp only [h, ite_true, Bool.false_eq_true, ite_false, Bool.false_and]
      ring
    · rw [dh_IP A σ hplp h, out_R3 σ hOP hL (D ω) hp (cX_of_ep x h), hgd,
        ep_false h (ch' := .minus) (out' := true) (by simp),
        ep_false h (ch' := .plus) (out' := true) (by simp),
        ep_false h (ch' := .minus) (out' := false) (by simp)]
      simp only [h, ite_true, Bool.false_eq_true, ite_false, Bool.false_and]
      ring
    · rw [dh_IM A σ hplp h, out_R2 σ hOP hL, hK,
        ep_false h (ch' := .minus) (out' := true) (by simp),
        ep_false h (ch' := .plus) (out' := false) (by simp),
        ep_false h (ch' := .plus) (out' := true) (by simp)]
      simp only [h, ite_true, Bool.false_eq_true, ite_false, Bool.false_and]
      ring
  · rw [ite_eq_right hb]
    have h1 : ep x .minus true p = false := by
      by_contra h
      have h' : ep x .minus true p = true := by simpa using h
      apply hb
      rw [cX_of_ep x h', Bool.true_and]
      by_contra h2
      have := zip_eq_of_snd hp (e₁_mem hL) (by simpa using h2)
      subst this
      exact absurd (ep_excl x h' (e₁_ep hOP hL)).1 (by simp)
    have h2 : ep x .plus false p = false := by
      by_contra h
      have h' : ep x .plus false p = true := by simpa using h
      apply hb
      rw [cX_of_ep x h', Bool.true_and]
      by_contra h2
      have := zip_eq_of_snd hp (e₁_mem hL) (by simpa using h2)
      subst this
      exact absurd (ep_excl x h' (e₁_ep hOP hL)).2 (by simp)
    have h3 : ep x .minus false p = false := by
      by_contra h
      have h' : ep x .minus false p = true := by simpa using h
      apply hb
      rw [cX_of_ep x h', Bool.true_and]
      by_contra h2
      have := zip_eq_of_snd hp (e₁_mem hL) (by simpa using h2)
      subst this
      exact absurd (ep_excl x h' (e₁_ep hOP hL)).1 (by simp)
    have h4 : (ep x .plus true p && p.2 != i₁) = false := by
      by_contra h
      have h' : (ep x .plus true p && p.2 != i₁) = true := by simpa using h
      obtain ⟨h5, h6⟩ := Bool.and_eq_true_iff.1 h'
      exact hb (by rw [cX_of_ep x h5, h6]; rfl)
    simp [h1, h2, h3, h4]

private theorem list_sum_neg {β : Type*} (l : List β) (f : β → ℂ) :
    (l.map fun x => -f x).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons q l ih => simp [ih]; ring

private theorem sum_ite_const {β : Type*} (l : List β) (P : β → Bool) (c : ℂ) :
    (l.map fun p => if P p = true then c else 0).sum = ((l.filter P).length : ℂ) * c := by
  induction l with
  | nil => simp
  | cons q l ih =>
    by_cases hq : P q = true
    · simp [hq, ih]; ring
    · simp [hq, ih]

omit [Fintype ι] [DecidableEq ι] in
private theorem len_OP {i₁ : ℕ} {is₂ : List ℕ} (hOP : Γ.edgeIdx x .plus true = i₁ :: is₂) :
    (Γ.comps.zipIdx.filter fun p => ep x .plus true p && p.2 != i₁).length = is₂.length := by
  have hnd : (i₁ :: is₂).Nodup := by
    rw [← hOP, edgeIdx_eq]
    exact (zip_snd_nodup Γ.comps).sublist ((List.filter_sublist).map _)
  have h : ((Γ.comps.zipIdx.filter fun p => ep x .plus true p && p.2 != i₁).map Prod.snd) =
      is₂ := by
    have e1 : (Γ.comps.zipIdx.filter fun p => ep x .plus true p && p.2 != i₁) =
        (Γ.comps.zipIdx.filter (ep x .plus true)).filter (fun p => p.2 != i₁) := by
      rw [List.filter_filter]
      congr 1
      funext p
      exact Bool.and_comm _ _
    have e2 : ((Γ.comps.zipIdx.filter (ep x .plus true)).filter (fun p => p.2 != i₁)).map
        Prod.snd = ((Γ.comps.zipIdx.filter (ep x .plus true)).map Prod.snd).filter (· != i₁) := by
      rw [List.filter_map]
      rfl
    rw [e1, e2, ← edgeIdx_eq, hOP]
    rw [List.filter_cons_of_neg (by simp), List.filter_eq_self.2]
    intro a ha
    have : a ≠ i₁ := fun h => (List.nodup_cons.1 hnd).1 (h ▸ ha)
    simpa using this
  rw [← h, List.length_map]

/-- `G_{β y₁}` times `-∂_{h_{βx}}` of the product of the edges at `x` other than `G_{x y₁}` and of
the rest: the four families of [I, (3.13)] and the derivative terms. -/
private theorem out_KEY (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hOP : Γ.edgeIdx x .plus true = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (σ' : Atom k (n + 1) → ι) (hσ' : σ' ∘ liftA 1 = σ)
    (β : ι) (hβ : σ' (newA 0) = β) (ω : Ω) :
    A.G ω β (σ e₁.y) * -(A.dh β (σ x) (fun ω' => Kx (cX x) Γ i₁ σ (D ω') *
        rv (D ω') σ (eraseIdxs (oXIdx x Γ) Γ.comps)) ω) =
      ((Γ.edgeIdx x .minus true).map fun j => rv (D ω) σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω β (σ e₁.y) * star (A.G ω β (σ (Γ.comps.getD j e₁).y))) *
          star (A.G ω (σ x) (σ x))).sum +
      ((Γ.edgeIdx x .plus false).map fun j => rv (D ω) σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω β (σ e₁.y) * A.G ω (σ (Γ.comps.getD j e₁).x) β) *
          A.G ω (σ x) (σ x)).sum +
      (is₂.length : ℂ) * (rv (D ω) σ (Γ.comps.eraseIdx i₁) * (A.G ω (σ x) β * A.G ω β (σ e₁.y))) +
      ((Γ.edgeIdx x .minus false).length : ℂ) * (rv (D ω) σ (Γ.comps.eraseIdx i₁) *
          (star (A.G ω β (σ x)) * A.G ω β (σ e₁.y))) +
      ((oDs x Γ i₁ e₁).map fun d => rv (D ω) σ' d).sum := by
  have hKt : A.Test fun ω' => Kx (cX x) Γ i₁ σ (D ω') :=
    test_listProd' A _ fun p hp => kx_test A σ hpl (fun _ h => cX_random x h) i₁ hp
  have hFb : ∀ c ∈ eraseIdxs (oXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  have hFt : A.Test fun ω' => rv (D ω') σ (eraseIdxs (oXIdx x Γ) Γ.comps) :=
    rv_test A σ _ fun c hc => (basB_of_plain (hFb c hc)).1
  have hdK : A.dh β (σ x) (fun ω' => Kx (cX x) Γ i₁ σ (D ω')) = fun ω' =>
      (Γ.comps.zipIdx.map fun p => A.dh β (σ x) (fun ω'' => kx (cX x) i₁ σ (D ω'') p) ω' *
        Kxq (cX x) Γ i₁ σ (D ω') p.2).sum :=
    dh_prod_rule A β (σ x) Prod.snd _ (zip_snd_nodup _) (fun p ω => kx (cX x) i₁ σ (D ω) p)
      (fun p hp => kx_test A σ hpl (fun _ h => cX_random x h) i₁ hp)
  have hdF := (dTerms_spec A σ' (newA 0) (liftA 1 x) _ (plain_bas_lift hFb 1)).2 ω
  simp only [rv_liftCs, hσ', hβ] at hdF
  rw [show σ' (liftA 1 x) = σ x by rw [← hσ']; rfl] at hdF
  have hD : ((oDs x Γ i₁ e₁).map fun d => rv (D ω) σ' d).sum =
      Kx (cX x) Γ i₁ σ (D ω) * A.G ω β (σ e₁.y) *
        ((dTerms (newA 0) (liftA 1 x) (liftCs 1 (eraseIdxs (oXIdx x Γ) Γ.comps))).map
          fun d => rv (D ω) σ' d).sum := by
    rw [oDs, List.map_map, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun d _ => ?_)
    simp only [Function.comp_apply, rv_append, rv_liftCs, hσ', out_R4, oSx, oGy, rv_cons,
      rv_nil, mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      Charge.apply, one_mul, mul_one, hβ]
    rw [show σ' (liftA 1 e₁.y) = σ e₁.y by rw [← hσ']; rfl]
    ring
  rw [dh_mul' A β (σ x) hKt hFt, hD, hdF, hdK]
  have hPP : ∀ p ∈ Γ.comps.zipIdx,
      -(A.dh β (σ x) (fun ω => kx (cX x) i₁ σ (D ω) p) ω) * Kxq (cX x) Γ i₁ σ (D ω) p.2 *
        rv (D ω) σ (eraseIdxs (oXIdx x Γ) Γ.comps) * A.G ω β (σ e₁.y) = _ :=
    fun p hp => out_PP A σ hpl hOP hL hp β ω
  have hsum : A.G ω β (σ e₁.y) * -((Γ.comps.zipIdx.map fun p =>
        A.dh β (σ x) (fun ω'' => kx (cX x) i₁ σ (D ω'') p) ω * Kxq (cX x) Γ i₁ σ (D ω) p.2).sum *
        rv (D ω) σ (eraseIdxs (oXIdx x Γ) Γ.comps)) =
      (Γ.comps.zipIdx.map fun p => -(A.dh β (σ x) (fun ω => kx (cX x) i₁ σ (D ω) p) ω) *
        Kxq (cX x) Γ i₁ σ (D ω) p.2 * rv (D ω) σ (eraseIdxs (oXIdx x Γ) Γ.comps) *
        A.G ω β (σ e₁.y)).sum := by
    rw [← List.sum_map_mul_right, ← list_sum_neg, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    ring
  rw [List.map_congr_left hPP] at hsum
  simp only [List.sum_map_add] at hsum
  have h1 := sum_filter_snd Γ.comps.zipIdx (ep x .minus true) (fun j =>
    rv (D ω) σ (eraseIdxs [i₁, j] Γ.comps) *
      (A.G ω β (σ e₁.y) * star (A.G ω β (σ (Γ.comps.getD j e₁).y))) * star (A.G ω (σ x) (σ x)))
  have h2 := sum_filter_snd Γ.comps.zipIdx (ep x .plus false) (fun j =>
    rv (D ω) σ (eraseIdxs [i₁, j] Γ.comps) *
      (A.G ω β (σ e₁.y) * A.G ω (σ (Γ.comps.getD j e₁).x) β) * A.G ω (σ x) (σ x))
  have h3 := sum_ite_const Γ.comps.zipIdx (fun p => ep x .plus true p && p.2 != i₁)
    (rv (D ω) σ (Γ.comps.eraseIdx i₁) * (A.G ω (σ x) β * A.G ω β (σ e₁.y)))
  have h4 := sum_ite_const Γ.comps.zipIdx (ep x .minus false)
    (rv (D ω) σ (Γ.comps.eraseIdx i₁) * (star (A.G ω β (σ x)) * A.G ω β (σ e₁.y)))
  rw [len_OP hOP] at h3
  rw [← edgeIdx_eq] at h1 h2
  have h5 : (Γ.comps.zipIdx.filter (ep x .minus false)).length =
      (Γ.edgeIdx x .minus false).length := by
    rw [edgeIdx_eq, List.length_map]
  rw [h5] at h4
  simp only []
  linear_combination hsum - h1 - h2 + h3 + h4

private theorem good_listSum {β : Type*} (l : List β) {f : β → Ω → ℂ} (h : ∀ q ∈ l, A.Good (f q)) :
    A.Good fun ω => (l.map fun q => f q ω).sum := by
  induction l with
  | nil => simpa using A.laws.good_const 0
  | cons z l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact A.laws.good_add _ _ (h z (List.mem_cons_self ..))
      (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- Linearity of `P_x` on a sum of the shape of [I, (3.13)]. -/
private theorem P_lin5 {γ : Type*} (X : ι) (l₁ l₂ : List ℕ) (l₅ : List γ) (f₁ f₂ : ℕ → Ω → ℂ)
    (f₅ : γ → Ω → ℂ) (c₃ c₄ : ℂ) (g₃ g₄ : Ω → ℂ) (h₁ : ∀ j ∈ l₁, A.Good (f₁ j))
    (h₂ : ∀ j ∈ l₂, A.Good (f₂ j)) (h₃ : A.Good g₃) (h₄ : A.Good g₄)
    (h₅ : ∀ d ∈ l₅, A.Good (f₅ d)) (ω : Ω) :
    PF.P X (fun ω' => (l₁.map fun j => f₁ j ω').sum + (l₂.map fun j => f₂ j ω').sum +
        c₃ * g₃ ω' + c₄ * g₄ ω' + (l₅.map fun d => f₅ d ω').sum) ω =
      (l₁.map fun j => PF.P X (f₁ j) ω).sum + (l₂.map fun j => PF.P X (f₂ j) ω).sum +
        c₃ * PF.P X g₃ ω + c₄ * PF.P X g₄ ω + (l₅.map fun d => PF.P X (f₅ d) ω).sum := by
  have g1 := good_listSum A l₁ h₁
  have g2 := good_listSum A l₂ h₂
  have g5 := good_listSum A l₅ h₅
  have g3 : A.Good fun ω => c₃ * g₃ ω := A.laws.good_mul _ _ (A.laws.good_const _) h₃
  have g4 : A.Good fun ω => c₄ * g₄ ω := A.laws.good_mul _ _ (A.laws.good_const _) h₄
  have g12 : A.Good fun ω => (l₁.map fun q => f₁ q ω).sum + (l₂.map fun q => f₂ q ω).sum :=
    A.laws.good_add _ _ g1 g2
  have g123 : A.Good fun ω => (l₁.map fun q => f₁ q ω).sum + (l₂.map fun q => f₂ q ω).sum +
      c₃ * g₃ ω := A.laws.good_add _ _ g12 g3
  have g1234 : A.Good fun ω => (l₁.map fun q => f₁ q ω).sum + (l₂.map fun q => f₂ q ω).sum +
      c₃ * g₃ ω + c₄ * g₄ ω := A.laws.good_add _ _ g123 g4
  rw [P_add' A g1234 g5, P_add' A g123 g4, P_add' A g12 g3, P_add' A g1 g2, P_cmul' A _ h₃,
    P_cmul' A _ h₄, P_listSum' A l₁ h₁, P_listSum' A l₂ h₂, P_listSum' A l₅ h₅]

private theorem bas_sub {cs : List (Comp (Atom k n))} (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true)
    (hs : ∀ c ∈ cs, c ∈ Γ.comps) : ∀ c ∈ cs, basB c = true :=
  fun c hc => (basB_of_plain (hpl c (hs c hc))).1

private theorem out_Pexp (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hOP : Γ.edgeIdx x .plus true = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (σ' : Atom k (n + 1) → ι) (hσ' : σ' ∘ liftA 1 = σ)
    (β : ι) (hβ : σ' (newA 0) = β) (ω : Ω) :
    PF.P (σ x) (fun ω' => A.G ω' β (σ e₁.y) * -(A.dh β (σ x) (fun ω'' => Kx (cX x) Γ i₁ σ (D ω'') *
        rv (D ω'') σ (eraseIdxs (oXIdx x Γ) Γ.comps)) ω')) ω =
      ((Γ.edgeIdx x .minus true).map fun j => PF.P (σ x) (fun ω' =>
          rv (D ω') σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω' β (σ e₁.y) * star (A.G ω' β (σ (Γ.comps.getD j e₁).y))) *
          star (A.G ω' (σ x) (σ x))) ω).sum +
      ((Γ.edgeIdx x .plus false).map fun j => PF.P (σ x) (fun ω' =>
          rv (D ω') σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω' β (σ e₁.y) * A.G ω' (σ (Γ.comps.getD j e₁).x) β) *
          A.G ω' (σ x) (σ x)) ω).sum +
      (is₂.length : ℂ) * PF.P (σ x) (fun ω' => rv (D ω') σ (Γ.comps.eraseIdx i₁) *
          (A.G ω' (σ x) β * A.G ω' β (σ e₁.y))) ω +
      ((Γ.edgeIdx x .minus false).length : ℂ) * PF.P (σ x) (fun ω' =>
          rv (D ω') σ (Γ.comps.eraseIdx i₁) * (star (A.G ω' β (σ x)) * A.G ω' β (σ e₁.y))) ω +
      ((oDs x Γ i₁ e₁).map fun d => PF.P (σ x) (fun ω' => rv (D ω') σ' d) ω).sum := by
  rw [P_congr' (fun ω' => out_KEY A σ hpl hOP hL σ' hσ' β hβ ω')]
  have hE : ∀ (is : List ℕ), A.Test fun ω' => rv (D ω') σ (eraseIdxs is Γ.comps) :=
    fun is => rv_test A σ _ (bas_sub hpl fun c hc => mem_eraseIdxs hc)
  have hR : A.Test fun ω' => rv (D ω') σ (Γ.comps.eraseIdx i₁) :=
    rv_test A σ _ (bas_sub hpl fun c hc => List.mem_of_mem_eraseIdx hc)
  have hFb : ∀ c ∈ eraseIdxs (oXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  refine P_lin5 A (σ x) _ _ _ _ _ _ _ _ _ _ (fun j _ => A.test_good _ ?_)
    (fun j _ => A.test_good _ ?_)
    (A.test_good _ ?_) (A.test_good _ ?_) (fun d hd => A.test_good _ ?_) ω
  · exact test_mul' A (test_mul' A (hE _) (test_mul' A (test_G A _ _)
      (test_star' A (test_G A _ _)))) (test_star' A (test_G A _ _))
  · exact test_mul' A (test_mul' A (hE _) (test_mul' A (test_G A _ _) (test_G A _ _)))
      (test_G A _ _)
  · exact test_mul' A hR (test_mul' A (test_G A _ _) (test_G A _ _))
  · exact test_mul' A hR (test_mul' A (test_star' A (test_G A _ _)) (test_G A _ _))
  · obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have hd'b := ((dTerms_spec A σ' (newA 0) (liftA 1 x) _ (plain_bas_lift hFb 1)).1 d' hd').1
    refine rv_test A σ' _ fun c hc => ?_
    rcases List.mem_append.1 hc with hc | hc
    · rcases List.mem_append.1 hc with hc | hc
      · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
        rw [basB_map]
        exact bas_sub hpl (fun c hc => mem_pickIdxs hc) c' hc'
      · exact (hd'b c hc).1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> rfl

end OutDeriv

/-! ## `×`-dotted edges at `x` -/

section Xdots

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k n : ℕ} {x : Atom k n} {Γ : Graph k n}

private theorem xdot_of {is : List ℕ} (h : Γ.xdotsAt x is = true) {i : ℕ} (hi : i ∈ is)
    {c : Comp (Atom k n)} (hc : Γ.comps[i]? = some c) :
    ∃ c' ∈ Γ.comps, c'.kind = .xdot ∧
      ((c'.x = x ∧ c'.y = (if c.x = x then c.y else c.x)) ∨
        (c'.x = (if c.x = x then c.y else c.x) ∧ c'.y = x)) := by
  unfold Graph.xdotsAt at h
  have h1 := List.all_eq_true.1 h i hi
  rw [hc] at h1
  simp only [Graph.hasXdot, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    Bool.or_eq_true] at h1
  obtain ⟨c', hc', hk, h2⟩ := h1
  refine ⟨c', hc', hk, ?_⟩
  by_cases hx : c.x = x
  · simpa [hx] using h2
  · simpa [hx] using h2

/-- The deterministic part vanishes when the ends of a `×`-dotted edge have the same label. -/
private theorem dv_xdot_zero (D₀ : Data ι) (σ : Atom k n → ι) {u : Atom k n}
    {c' : Comp (Atom k n)} (hc' : c' ∈ Γ.comps) (hk : c'.kind = .xdot)
    (hxy : (c'.x = x ∧ c'.y = u) ∨ (c'.x = u ∧ c'.y = x)) (hσ : σ x = σ u) :
    dv D₀ σ Γ.comps = 0 := by
  unfold dv
  refine List.prod_eq_zero (List.mem_map.2 ⟨c', List.mem_filter.2 ⟨hc', by simp [hk,
    Kind.isRandom]⟩, ?_⟩)
  simp only [Comp.val, hk]
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2, hσ]

end Xdots

private theorem list_finset_comm {ι β : Type*} [Fintype ι] (l : List β) (f : β → ι → ℂ) :
    (l.map fun j => ∑ α, f j α).sum = ∑ α, (l.map fun j => f j α).sum := by
  induction l with
  | nil => simp
  | cons j l ih => simp [ih, Finset.sum_add_distrib]

/-! ## Case (i): the identity at one labelling -/

section OutCore

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ} {x : Atom k n} {Γ : Graph k n}

/-- [I, (3.11)] in the form of the graphs of `multiEOut`, at one labelling `σ` of the atoms of the
input graph (`τ α` labels the new atom by `α`). -/
private theorem out_core (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hOP : Γ.edgeIdx x .plus true = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (hX : Γ.xdotsAt x (oXIdx x Γ) = true) (σ : Atom k n → ι)
    (τ : ι → Atom k (n + 1) → ι) (hτ1 : ∀ α, τ α ∘ liftA 1 = σ) (hτ2 : ∀ α, τ α (newA 0) = α)
    (ω : Ω) :
    Γ.coeff.eval (msc A.z) * dv (D ω) σ Γ.comps * rv (D ω) σ Γ.comps =
      ((Γ.edgeIdx x .minus true).map fun j => ∑ α, msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω' α (σ e₁.y) * star (A.G ω' α (σ (Γ.comps.getD j e₁).y))) *
          star (A.G ω' (σ x) (σ x))) ω).sum +
      ((Γ.edgeIdx x .plus false).map fun j => ∑ α, msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω' α (σ e₁.y) * A.G ω' (σ (Γ.comps.getD j e₁).x) α) *
          A.G ω' (σ x) (σ x)) ω).sum +
      ∑ α, msc A.z * Γ.coeff.eval (msc A.z) * (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps * (A.G ω' α α - msc A.z)) ω +
      ∑ α, (is₂.length : ℂ) * msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ (Γ.comps.eraseIdx i₁) *
          (A.G ω' (σ x) α * A.G ω' α (σ e₁.y))) ω +
      ∑ α, ((Γ.edgeIdx x .minus false).length : ℂ) * msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ (Γ.comps.eraseIdx i₁) *
          (star (A.G ω' α (σ x)) * A.G ω' α (σ e₁.y))) ω +
      ((oDs x Γ i₁ e₁).map fun d => ∑ α, msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') (τ α) d) ω).sum +
      Γ.coeff.eval (msc A.z) * dv (D ω) σ Γ.comps *
        PF.op .Q (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω := by
  set c := Γ.coeff.eval (msc A.z)
  set Det := dv (D ω) σ Γ.comps
  have hFb : ∀ c ∈ eraseIdxs (oXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  -- `x` and `y₁` with the same label: every term vanishes
  have he₁ := ep_spec x (e₁_ep hOP hL)
  by_cases hXY : σ x = σ e₁.y
  · have hx1 : i₁ ∈ oXIdx x Γ := by
      rw [oXIdx, hOP]
      simp
    obtain ⟨c', hc', hk, hxy⟩ := xdot_of hX hx1 hL
    rw [ite_eq_left (he₁.2.1 rfl).1] at hxy
    have h0 : Det = 0 := dv_xdot_zero (D ω) σ hc' hk hxy hXY
    simp [h0]
  -- the integration by parts in `P_x`
  have hpe : (e₁.isPlainB = true) := hpl e₁ (List.mem_of_getElem? hL)
  have hve : ∀ ω', Comp.val (D ω') σ e₁ = A.G ω' (σ x) (σ e₁.y) := by
    intro ω'
    rw [val_edge A σ hpe he₁.1, (he₁.2.1 rfl).1]
    rfl
  set K : Ω → ℂ := fun ω' => Kx (cX x) Γ i₁ σ (D ω') * rv (D ω') σ (eraseIdxs (oXIdx x Γ) Γ.comps)
    with hKdef
  have hKt : A.Test K :=
    test_mul' A (test_listProd' A _ fun p hp => kx_test A σ hpl (fun _ h => cX_random x h) i₁ hp)
      (rv_test A σ _ fun c hc => (basB_of_plain (hFb c hc)).1)
  have hR1 : ∀ ω', rv (D ω') σ Γ.comps = A.G ω' (σ x) (σ e₁.y) * K ω' := by
    intro ω'
    rw [out_R1 σ hOP hL, hve]
  have hP : PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω =
      msc A.z * ∑ β, (A.S (σ x) β : ℂ) *
        PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps * (A.G ω' β β - msc A.z)) ω +
      msc A.z * ∑ β, (A.S (σ x) β : ℂ) * PF.P (σ x) (fun ω' => A.G ω' β (σ e₁.y) *
        -(A.dh β (σ x) K ω')) ω := by
    rw [P_congr' hR1, ibp_row A (σ x) (σ e₁.y) hKt ω, ite_eq_right hXY]
    have h1 : ∀ β, PF.P (σ x) (fun ω' => (A.G ω' β β - msc A.z) * A.G ω' (σ x) (σ e₁.y) *
        K ω') ω = PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps * (A.G ω' β β - msc A.z)) ω :=
      fun β => by
        rw [P_congr' (g := fun ω' => rv (D ω') σ Γ.comps * (A.G ω' β β - msc A.z))
          fun ω' => by rw [hR1]; ring]
    have h2 : ∀ β, PF.P (σ x) (fun ω' => A.G ω' β (σ e₁.y) * A.dh β (σ x) K ω') ω =
        -PF.P (σ x) (fun ω' => A.G ω' β (σ e₁.y) * -(A.dh β (σ x) K ω')) ω := fun β => by
      rw [← P_neg' A (A.test_good _ (test_mul' A (test_G A _ _)
        (test_neg' A (test_dh' A _ _ hKt))))]
      rw [P_congr' (g := fun ω' => -(A.G ω' β (σ e₁.y) * -(A.dh β (σ x) K ω'))) fun ω' => by
        ring]
    simp only [h1, h2]
    simp only [mul_neg, Finset.sum_neg_distrib]
    ring
  rw [show rv (D ω) σ Γ.comps = PF.op .Q (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω +
    PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω by rw [Q_apply']; ring, hP]
  simp only [hKdef, fun β => out_Pexp A σ hpl hOP hL (τ β) (hτ1 β) β (hτ2 β) ω]
  rw [list_finset_comm, list_finset_comm, list_finset_comm]
  simp only [List.sum_map_mul_left, ← Finset.sum_add_distrib]
  rw [add_comm _ (c * Det * PF.op .Q (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω), mul_add]
  simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

end OutCore

private theorem triple_sum {β : Type*} (l : List β) (f₁ f₂ f₃ g : β → ℂ)
    (h : ∀ j ∈ l, f₁ j + f₂ j + f₃ j = g j) :
    (l.map f₁).sum + (l.map f₂).sum + (l.map f₃).sum = (l.map g).sum := by
  rw [← List.sum_map_add, ← List.sum_map_add]
  exact congrArg _ (List.map_congr_left h)

/-! ## Case (i): value of `multiEOut` -/

section OutValue

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ}

include A in
/-- Case (i) of [I, Def 3.11]: the formal sum of `multiEOut` has the value of the graph. -/
private theorem multiEOut_valR (x : Atom k n) (Γ : Graph k n)
    (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {E : TExpansion k n} (hE : multiEOut x Γ = some E)
    (e : Fin k → ι) (ω : Ω) : S PF D e ω E = Γ.valR PF D e ω := by
  obtain ⟨i₁, is₂, e₁, hOP, hL, hX, rfl⟩ := multiEOut_some x Γ hE
  have hU : Unl Γ.comps := plain_Unl hpl
  have hr : ∃ c ∈ Γ.comps, c.kind.isRandom = true :=
    ⟨e₁, List.mem_of_getElem? hL, by rw [(ep_spec x (e₁_ep hOP hL)).1]; rfl⟩
  unfold oOut
  simp only [S_append, S_map_t1, S_t1, S_t0, S_ite, ite_sum]
  rw [valR_T0, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hdj : ∀ (ch : Charge) (out : Bool), ∀ j ∈ Γ.edgeIdx x ch out,
      dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] Γ.comps) = dv (D ω) (Sum.elim e s) Γ.comps := by
    intro ch out j hj
    rw [edgeIdx_eq] at hj
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hj
    exact out_D3 _ hOP hL (D ω) (List.mem_filter.1 hq).1 (cX_of_ep x (List.mem_filter.1 hq).2)
  have hdE := out_D1 (Sum.elim e s) hOP hL (D ω)
  have hFb : ∀ c ∈ eraseIdxs (oXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  have hdD : ∀ d ∈ oDs x Γ i₁ e₁, ∀ α, dv (D ω) (Sum.elim e (Fin.append s ![α])) d =
      dv (D ω) (Sum.elim e s) Γ.comps * (A.S (Sum.elim e s x) α : ℂ) := by
    intro d hd α
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have h2 := ((dTerms_spec A (Sum.elim e (Fin.append s ![α])) (newA 0) (liftA 1 x) _
      (plain_bas_lift hFb 1)).1 d' hd').2 (D ω)
    rw [dv_liftCs, elim_append_comp_liftA, out_D4] at h2
    simp only [dv_append, dv_liftCs, elim_append_comp_liftA, out_D5, h2, oSx, oGy, dv_cons,
      dv_nil, mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  have hM := triple_sum _ _ _ _ _ fun j (hj : j ∈ Γ.edgeIdx x .minus true) =>
    (out_BM A x Γ i₁ e₁ e ω hU j s).trans (by rw [hdj .minus true j hj])
  have hP := triple_sum _ _ _ _ _ fun j (hj : j ∈ Γ.edgeIdx x .plus false) =>
    (out_BP A x Γ i₁ e₁ e ω hU j s).trans (by rw [hdj .plus false j hj])
  have hL3 := out_BL A x Γ e ω hU s
  have hE1 := out_BE1 A x Γ i₁ e₁ e ω hU (is₂.isEmpty = true) is₂.length
    (fun h => by simpa using h) s
  have hE2 := out_BE2 A x Γ i₁ e₁ e ω hU ((Γ.edgeIdx x .minus false).length = 0)
    (Γ.edgeIdx x .minus false).length id s
  rw [hdE] at hE1 hE2
  have hD := (out_BD A x Γ i₁ e₁ e ω hpl s).trans (congrArg List.sum (List.map_congr_left
    fun d hd => Finset.sum_congr rfl fun α _ => by rw [hdD d hd α]))
  have hQ := out_BQ A x Γ e ω hU hr s
  have hΓ := T0_self A Γ e ω hU s
  have hcore := out_core A hpl hOP hL hX (Sum.elim e s) (fun α => Sum.elim e (Fin.append s ![α]))
    (fun α => elim_append_comp_liftA e s ![α]) (fun α => by simp) ω
  linear_combination hM + hP + hL3 + hE1 + hE2 + hD + hQ - hΓ - hcore

end OutValue

/-! ## The graphs of the multi-edge expansion, case (iii) -/

section InDefs

variable {k n : ℕ} (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ) (e₁ : Comp (Atom k n))

/-- The indices of the solid edges entering `x`, in the order of case (iii). -/
private def iXIdx : List ℕ := Γ.edgeIdx x .plus false ++ Γ.edgeIdx x .minus false

/-- The solid edge `G_{w₁ α}`. -/
private def iGw : Comp (Atom k (n + 1)) := mkC (.G .plus) (liftA 1 e₁.x) (newA 0)

/-- A main term of [I, (3.14)] for the edge `Ḡ_{w' x}` at position `j`: the components other than
`G_{w₁ x}` and `Ḡ_{w' x}`, and `s_{xα} G_{w₁ α} Ḡ_{w' α}`. -/
private def iBaseM (j : ℕ) : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
    [oSx x, iGw e₁, mkC (.G .minus) (liftA 1 ((Γ.comps.getD j e₁).x)) (newA 0)]

/-- The `(k₃ - 1)` term of [I, (3.14)]: the components other than `G_{w₁ x}`, and
`s_{xα} G_{w₁ α} G_{αx}`. -/
private def iE1 : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (Γ.comps.eraseIdx i₁) ++ [oSx x, iGw e₁, mkC (.G .plus) (newA 0) (liftA 1 x)]

/-- The derivative terms of [I, (3.14)]: the edges entering `x` other than `G_{w₁ x}`, one graph of
`-∂_{h_{xα}}` of the other components, and `s_{xα} G_{w₁ α}`. -/
private def iDs : List (List (Comp (Atom k (n + 1)))) :=
  (dTerms (liftA 1 x) (newA 0) (liftCs 1 (eraseIdxs (iXIdx x Γ) Γ.comps))).map fun d =>
    liftCs 1 (pickIdxs ((iXIdx x Γ).filter (· != i₁)) Γ.comps) ++ d ++ [oSx x, iGw e₁]

/-- The formal sum of `multiEIn`. -/
private def iOut : TExpansion k n :=
  (Γ.edgeIdx x .minus false).map (fun j => t1 (iBaseM x Γ i₁ e₁ j) (cm * cmb * Γ.coeff)) ++
    (Γ.edgeIdx x .minus false).map (fun j => t1 (iBaseM x Γ i₁ e₁ j ++
      [mkC (.light .minus) (liftA 1 x) (liftA 1 x)]) (cm * Γ.coeff)) ++
    [t1 (oL3 x Γ) (cm * Γ.coeff)] ++
    (if is₂.isEmpty then [] else [t1 (iE1 x Γ i₁ e₁) ((is₂.length : Coeff) * cm * Γ.coeff)]) ++
    (iDs x Γ i₁ e₁).map (fun d => t1 d (cm * Γ.coeff)) ++
    [⟨n, ⟨labelQs x Γ.comps, Γ.coeff⟩, id⟩] ++
    (Γ.edgeIdx x .minus false).map (fun j => t1 (labelQs (liftA 1 x) (iBaseM x Γ i₁ e₁ j ++
      [mkC (.weight .minus) (liftA 1 x) (liftA 1 x)])) (-cm * Γ.coeff)) ++
    [t1 (labelQs (liftA 1 x) (oL3 x Γ)) (-cm * Γ.coeff)] ++
    (if is₂.isEmpty then [] else
      [t1 (labelQs (liftA 1 x) (iE1 x Γ i₁ e₁)) (-(is₂.length : Coeff) * cm * Γ.coeff)]) ++
    (iDs x Γ i₁ e₁).map (fun d => t1 (labelQs (liftA 1 x) d) (-cm * Γ.coeff))

private theorem multiEIn_some {E : TExpansion k n} (h : multiEIn x Γ = some E) :
    ∃ i₁ is₂ e₁, Γ.edgeIdx x .plus false = i₁ :: is₂ ∧ Γ.comps[i₁]? = some e₁ ∧
      Γ.xdotsAt x (iXIdx x Γ) = true ∧ E = iOut x Γ i₁ is₂ e₁ := by
  unfold multiEIn at h
  split at h
  · exact absurd h (by simp)
  rename_i i₁ is₂ hIP
  split at h
  · exact absurd h (by simp)
  rename_i e₁ hL
  dsimp only at h
  rw [ite_eq_iff] at h
  rcases h with ⟨_, h⟩ | ⟨hX, h⟩
  · exact absurd h (by simp)
  refine ⟨i₁, is₂, e₁, hIP, hL, by simpa [iXIdx] using hX, ?_⟩
  exact (Option.some.inj h).symm

end InDefs

section InPos

variable {k n : ℕ} (x : Atom k n)

/-- The component at a position is a solid edge entering `x` (self-loops excluded). -/
private def cI (p : Comp (Atom k n) × ℕ) : Bool := ep x .plus false p || ep x .minus false p

private theorem cI_random {p : Comp (Atom k n) × ℕ} (h : cI x p = true) :
    p.1.kind.isRandom = true := by
  unfold cI at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h <;> rw [(ep_spec x h).1] <;> rfl

private theorem contains_iXIdx (Γ : Graph k n) {p : Comp (Atom k n) × ℕ}
    (hp : p ∈ Γ.comps.zipIdx) : (iXIdx x Γ).contains p.2 = cI x p := by
  simp only [iXIdx, edgeIdx_eq, List.contains_append, contains_filter_snd hp, cI]

end InPos

section InProd

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k n : ℕ} {x : Atom k n} {Γ : Graph k n}
  {i₁ : ℕ} (σ : Atom k n → ι) {is₂ : List ℕ} {e₁ : Comp (Atom k n)}

omit [Fintype ι] [DecidableEq ι] in
private theorem in_hxI : ∀ p ∈ Γ.comps.zipIdx, (iXIdx x Γ).contains p.2 = cI x p :=
  fun _ hp => contains_iXIdx x Γ hp

private theorem in_hcR : ∀ p : Comp (Atom k n) × ℕ, cI x p = true → p.1.kind.isRandom = true :=
  fun _ h => cI_random x h

variable (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂) (hL : Γ.comps[i₁]? = some e₁)
include hIP hL

omit [Fintype ι] [DecidableEq ι] in
private theorem in_e₁_ep : ep x .plus false (e₁, i₁) = true := by
  have h : i₁ ∈ Γ.edgeIdx x .plus false := by rw [hIP]; exact List.mem_cons_self ..
  rw [edgeIdx_eq] at h
  exact (mem_filter_snd (mem_zip_of_get hL)).1 h

omit [Fintype ι] [DecidableEq ι] in
private theorem in_e₁_cI : cI x (e₁, i₁) = true := by
  simp [cI, in_e₁_ep hIP hL]

private theorem in_R1 (D₀ : Data ι) :
    rv D₀ σ Γ.comps = Comp.val D₀ σ e₁ *
      (Kx (cI x) Γ i₁ σ D₀ * rv D₀ σ (eraseIdxs (iXIdx x Γ) Γ.comps)) :=
  gR1 σ in_hxI in_hcR (mem_zip_of_get hL) (in_e₁_cI hIP hL) D₀

private theorem in_R2 (D₀ : Data ι) :
    rv D₀ σ (Γ.comps.eraseIdx i₁) =
      Kx (cI x) Γ i₁ σ D₀ * rv D₀ σ (eraseIdxs (iXIdx x Γ) Γ.comps) :=
  gR2 σ in_hxI in_hcR (mem_zip_of_get hL) (in_e₁_cI hIP hL) D₀

private theorem in_R3 (D₀ : Data ι) {q : Comp (Atom k n) × ℕ} (hq : q ∈ Γ.comps.zipIdx)
    (hqc : cI x q = true) :
    rv D₀ σ (eraseIdxs [i₁, q.2] Γ.comps) =
      Kxq (cI x) Γ i₁ σ D₀ q.2 * rv D₀ σ (eraseIdxs (iXIdx x Γ) Γ.comps) :=
  gR3 σ in_hxI in_hcR (mem_zip_of_get hL) (in_e₁_cI hIP hL) D₀ hq hqc

private theorem in_D1 (D₀ : Data ι) : dv D₀ σ (Γ.comps.eraseIdx i₁) = dv D₀ σ Γ.comps :=
  gD1 σ in_hcR (mem_zip_of_get hL) (in_e₁_cI hIP hL) D₀

private theorem in_D3 (D₀ : Data ι) {q : Comp (Atom k n) × ℕ} (hq : q ∈ Γ.comps.zipIdx)
    (hqc : cI x q = true) : dv D₀ σ (eraseIdxs [i₁, q.2] Γ.comps) = dv D₀ σ Γ.comps :=
  gD3 σ in_hcR (mem_zip_of_get hL) (in_e₁_cI hIP hL) D₀ hq hqc

omit hIP hL in
private theorem in_R4 (D₀ : Data ι) :
    rv D₀ σ (pickIdxs ((iXIdx x Γ).filter (· != i₁)) Γ.comps) = Kx (cI x) Γ i₁ σ D₀ :=
  gR4 σ in_hxI in_hcR D₀

omit hIP hL in
private theorem in_D4 (D₀ : Data ι) :
    dv D₀ σ (eraseIdxs (iXIdx x Γ) Γ.comps) = dv D₀ σ Γ.comps :=
  gD4 σ in_hxI in_hcR D₀

omit hIP hL in
private theorem in_D5 (D₀ : Data ι) :
    dv D₀ σ (pickIdxs ((iXIdx x Γ).filter (· != i₁)) Γ.comps) = 1 :=
  gD5 σ in_hxI in_hcR D₀

end InProd

section InBlocks

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ} (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ)
  (e₁ : Comp (Atom k n)) (e : Fin k → ι) (ω : Ω)

private theorem in_BM (hU : Unl Γ.comps) (j : ℕ) (s : Fin n → ι) :
    T1 PF D e ω ⟨iBaseM x Γ i₁ e₁ j, cm * cmb * Γ.coeff⟩ s +
      T1 PF D e ω ⟨iBaseM x Γ i₁ e₁ j ++ [mkC (.light .minus) (liftA 1 x) (liftA 1 x)],
        cm * Γ.coeff⟩ s +
      T1 PF D e ω ⟨labelQs (liftA 1 x) (iBaseM x Γ i₁ e₁ j ++
        [mkC (.weight .minus) (liftA 1 x) (liftA 1 x)]), -cm * Γ.coeff⟩ s =
    ∑ α, msc A.z * Γ.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] Γ.comps) * (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] Γ.comps) *
        (A.G ω' (Sum.elim e s e₁.x) α * star (A.G ω' (Sum.elim e s (Γ.comps.getD j e₁).x) α)) *
        star (A.G ω' (Sum.elim e s x) (Sum.elim e s x))) ω := by
  simp only [T1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hUM : Unl (iBaseM x Γ i₁ e₁ j) := by
    unfold iBaseM oSx iGw
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => mem_eraseIdxs hc),
      by simp [Unl, mkC]⟩
  rw [termR_triple A (liftA 1 x) .minus _ _ _ _ hUM
    (fun z => by simp only [ceval_mul, ceval_cm, ceval_cmb, Charge.apply]; ring)
    (fun z => by simp only [ceval_mul, ceval_neg, ceval_cm]; ring)]
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (iBaseM x Γ i₁ e₁ j) *
      Charge.minus.apply (A.G ω' (Sum.elim e (Fin.append s ![α]) (liftA 1 x))
        (Sum.elim e (Fin.append s ![α]) (liftA 1 x))) =
      rv (D ω') (Sum.elim e s) (eraseIdxs [i₁, j] Γ.comps) *
        (A.G ω' (Sum.elim e s e₁.x) α * star (A.G ω' (Sum.elim e s (Γ.comps.getD j e₁).x) α)) *
        star (A.G ω' (Sum.elim e s x) (Sum.elim e s x)) := by
    intro ω'
    simp only [iBaseM, oSx, iGw, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (iBaseM x Γ i₁ e₁ j) =
      dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] Γ.comps) * (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [iBaseM, oSx, iGw, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  rw [P_congr' hrv, hdv, elim_append_liftA, m_eq A, ceval_mul, ceval_cm]

private theorem in_BE1 (hU : Unl Γ.comps) (b : Prop) [Decidable b] (a : ℕ) (hb : b → a = 0)
    (s : Fin n → ι) :
    (if b then 0 else T1 PF D e ω ⟨iE1 x Γ i₁ e₁, (a : Coeff) * cm * Γ.coeff⟩ s) +
      (if b then 0 else
        T1 PF D e ω ⟨labelQs (liftA 1 x) (iE1 x Γ i₁ e₁), -(a : Coeff) * cm * Γ.coeff⟩ s) =
    ∑ α, (a : ℂ) * msc A.z * Γ.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (Γ.comps.eraseIdx i₁) * (A.S (Sum.elim e s x) α : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) (Γ.comps.eraseIdx i₁) *
        (A.G ω' (Sum.elim e s e₁.x) α * A.G ω' α (Sum.elim e s x))) ω := by
  by_cases hb' : b
  · simp [hb', hb hb']
  simp only [hb', ite_false, T1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hU3 : Unl (iE1 x Γ i₁ e₁) := by
    unfold iE1 oSx iGw
    exact Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub hU fun c hc => List.mem_of_mem_eraseIdx hc),
      by simp [Unl, mkC]⟩
  rw [termR_pair0 (liftA 1 x) _ _ _ hU3
    ⟨iGw e₁, List.mem_append_right _ (by simp), rfl⟩
    (fun z => by simp only [ceval_mul, ceval_neg, ceval_cm]; ring)]
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α])) (iE1 x Γ i₁ e₁) =
      rv (D ω') (Sum.elim e s) (Γ.comps.eraseIdx i₁) *
        (A.G ω' (Sum.elim e s e₁.x) α * A.G ω' α (Sum.elim e s x)) := by
    intro ω'
    simp only [iE1, oSx, iGw, rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero, Charge.apply]
    ring
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α])) (iE1 x Γ i₁ e₁) =
      dv (D ω) (Sum.elim e s) (Γ.comps.eraseIdx i₁) * (A.S (Sum.elim e s x) α : ℂ) := by
    simp only [iE1, oSx, iGw, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
      mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  rw [P_congr' hrv, hdv, elim_append_liftA, m_eq A, ceval_mul, ceval_mul, ceval_cm, ceval_nat]

private theorem in_BD (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) (s : Fin n → ι) :
    ((iDs x Γ i₁ e₁).map fun d => T1 PF D e ω ⟨d, cm * Γ.coeff⟩ s).sum +
      ((iDs x Γ i₁ e₁).map fun d =>
        T1 PF D e ω ⟨labelQs (liftA 1 x) d, -cm * Γ.coeff⟩ s).sum =
    ((iDs x Γ i₁ e₁).map fun d => ∑ α, msc A.z * Γ.coeff.eval (msc A.z) *
      dv (D ω) (Sum.elim e (Fin.append s ![α])) d *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e (Fin.append s ![α])) d) ω).sum := by
  rw [← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun d hd => ?_)
  simp only [T1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
  have hpl' : ∀ c ∈ eraseIdxs (iXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  have hd'U := ((dTerms_spec A (Sum.elim e (Fin.append s ![α])) (liftA 1 x) (newA 0) _
    (plain_bas_lift hpl' 1)).1 d' hd').1
  have hU3 : Unl (liftCs 1 (pickIdxs ((iXIdx x Γ).filter (· != i₁)) Γ.comps) ++ d' ++
      [oSx x, iGw e₁]) := by
    refine Unl_append.2 ⟨Unl_append.2 ⟨Unl_liftCs 1 (Unl_sub (plain_Unl hpl) fun c hc =>
      mem_pickIdxs hc), fun c hc => (hd'U c hc).2⟩, by simp [Unl, oSx, iGw, mkC]⟩
  rw [termR_pair0 (liftA 1 x) _ _ _ hU3
    ⟨iGw e₁, List.mem_append_right _ (by simp), rfl⟩
    (fun z => by simp only [ceval_mul, ceval_neg, ceval_cm]; ring),
    elim_append_liftA, m_eq A, ceval_mul, ceval_cm]

end InBlocks

/-! ## Case (iii): `-∂_{h_{xα}}` of the edges entering `x` -/

section InDeriv

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ} {x : Atom k n} {Γ : Graph k n} (σ : Atom k n → ι)

private theorem dh_IPx {p : Comp (Atom k n) × ℕ} (hc : p.1.isPlainB = true)
    (h : ep x .plus false p = true) (β : ι) :
    A.dh (σ x) β (fun ω => Comp.val (D ω) σ p.1) =
      fun ω => -(Comp.val (D ω) σ p.1 * A.G ω β (σ x)) := by
  obtain ⟨hk, -, hi⟩ := ep_spec x h
  rw [fun_edge A σ hc hk]
  simp only [Charge.apply, dh_G', (hi rfl).1, val_edge A σ hc hk]

private theorem dh_IMx {p : Comp (Atom k n) × ℕ} (hc : p.1.isPlainB = true)
    (h : ep x .minus false p = true) (β : ι) :
    A.dh (σ x) β (fun ω => Comp.val (D ω) σ p.1) =
      fun ω => -(star (A.G ω (σ p.1.x) β) * star (A.G ω (σ x) (σ x))) := by
  obtain ⟨hk, -, hi⟩ := ep_spec x h
  rw [fun_edge A σ hc hk]
  simp only [Charge.apply, dh_starG', (hi rfl).1]

/-- The term of `-∂_{h_{xβ}}` at one position, times the other factors, sorted into the
families of [I, (3.14)]. -/
private theorem in_PP (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) {p : Comp (Atom k n) × ℕ} (hp : p ∈ Γ.comps.zipIdx)
    (β : ι) (ω : Ω) :
    -(A.dh (σ x) β (fun ω => kx (cI x) i₁ σ (D ω) p) ω) * Kxq (cI x) Γ i₁ σ (D ω) p.2 *
        rv (D ω) σ (eraseIdxs (iXIdx x Γ) Γ.comps) * A.G ω (σ e₁.x) β =
      (if ep x .minus false p = true then rv (D ω) σ (eraseIdxs [i₁, p.2] Γ.comps) *
          (A.G ω (σ e₁.x) β * star (A.G ω (σ (Γ.comps.getD p.2 e₁).x) β)) *
          star (A.G ω (σ x) (σ x)) else 0) +
      (if (ep x .plus false p && p.2 != i₁) = true then rv (D ω) σ (Γ.comps.eraseIdx i₁) *
          (A.G ω (σ e₁.x) β * A.G ω β (σ x)) else 0) := by
  have hplp := hpl _ (fst_mem_of_zip hp)
  rw [dh_kx A σ (cI x) i₁ p]
  by_cases hb : (cI x p && p.2 != i₁) = true
  · rw [ite_eq_left hb]
    obtain ⟨hc, hne⟩ := Bool.and_eq_true_iff.1 hb
    have hK := Kx_single (cI x) Γ i₁ σ (D ω) hp
    rw [kx, ite_eq_left hb] at hK
    have hgd := getD_of_zip hp e₁
    simp only [cI, Bool.or_eq_true] at hc
    rcases hc with h | h
    · rw [dh_IPx A σ hplp h, in_R2 σ hIP hL, hK,
        ep_false h (ch' := .minus) (out' := false) (by simp)]
      simp only [h, hne, Bool.and_self, ite_true, Bool.false_eq_true, ite_false]
      ring
    · rw [dh_IMx A σ hplp h, in_R3 σ hIP hL (D ω) hp (by simp [cI, h]), hgd,
        ep_false h (ch' := .plus) (out' := false) (by simp)]
      simp only [h, ite_true, Bool.false_eq_true, ite_false, Bool.false_and]
      ring
  · rw [ite_eq_right hb]
    have h1 : ep x .minus false p = false := by
      by_contra h
      have h' : ep x .minus false p = true := by simpa using h
      apply hb
      rw [show cI x p = true by simp [cI, h'], Bool.true_and]
      by_contra h2
      have := zip_eq_of_snd hp (mem_zip_of_get hL) (by simpa using h2)
      subst this
      exact absurd (ep_excl x h' (in_e₁_ep hIP hL)).1 (by simp)
    have h4 : (ep x .plus false p && p.2 != i₁) = false := by
      by_contra h
      have h' : (ep x .plus false p && p.2 != i₁) = true := by simpa using h
      obtain ⟨h5, h6⟩ := Bool.and_eq_true_iff.1 h'
      exact hb (by rw [show cI x p = true by simp [cI, h5], h6]; rfl)
    simp [h1, h4]

omit [Fintype ι] [DecidableEq ι] in
private theorem len_IP {i₁ : ℕ} {is₂ : List ℕ} (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂) :
    (Γ.comps.zipIdx.filter fun p => ep x .plus false p && p.2 != i₁).length = is₂.length := by
  have hnd : (i₁ :: is₂).Nodup := by
    rw [← hIP, edgeIdx_eq]
    exact (zip_snd_nodup Γ.comps).sublist ((List.filter_sublist).map _)
  have h : ((Γ.comps.zipIdx.filter fun p => ep x .plus false p && p.2 != i₁).map Prod.snd) =
      is₂ := by
    have e1 : (Γ.comps.zipIdx.filter fun p => ep x .plus false p && p.2 != i₁) =
        (Γ.comps.zipIdx.filter (ep x .plus false)).filter (fun p => p.2 != i₁) := by
      rw [List.filter_filter]
      congr 1
      funext p
      exact Bool.and_comm _ _
    have e2 : ((Γ.comps.zipIdx.filter (ep x .plus false)).filter (fun p => p.2 != i₁)).map
        Prod.snd = ((Γ.comps.zipIdx.filter (ep x .plus false)).map Prod.snd).filter (· != i₁) := by
      rw [List.filter_map]
      rfl
    rw [e1, e2, ← edgeIdx_eq, hIP]
    rw [List.filter_cons_of_neg (by simp), List.filter_eq_self.2]
    intro a ha
    have : a ≠ i₁ := fun h => (List.nodup_cons.1 hnd).1 (h ▸ ha)
    simpa using this
  rw [← h, List.length_map]

/-- `G_{w₁ β}` times `-∂_{h_{xβ}}` of the product of the edges entering `x` other than
`G_{w₁ x}` and of the rest: the families of [I, (3.14)] and the derivative terms. -/
private theorem in_KEY (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (σ' : Atom k (n + 1) → ι) (hσ' : σ' ∘ liftA 1 = σ)
    (β : ι) (hβ : σ' (newA 0) = β) (ω : Ω) :
    A.G ω (σ e₁.x) β * -(A.dh (σ x) β (fun ω' => Kx (cI x) Γ i₁ σ (D ω') *
        rv (D ω') σ (eraseIdxs (iXIdx x Γ) Γ.comps)) ω) =
      ((Γ.edgeIdx x .minus false).map fun j => rv (D ω) σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω (σ e₁.x) β * star (A.G ω (σ (Γ.comps.getD j e₁).x) β)) *
          star (A.G ω (σ x) (σ x))).sum +
      (is₂.length : ℂ) * (rv (D ω) σ (Γ.comps.eraseIdx i₁) * (A.G ω (σ e₁.x) β * A.G ω β (σ x))) +
      ((iDs x Γ i₁ e₁).map fun d => rv (D ω) σ' d).sum := by
  have hKt : A.Test fun ω' => Kx (cI x) Γ i₁ σ (D ω') :=
    test_listProd' A _ fun p hp => kx_test A σ hpl in_hcR i₁ hp
  have hFb : ∀ c ∈ eraseIdxs (iXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  have hFt : A.Test fun ω' => rv (D ω') σ (eraseIdxs (iXIdx x Γ) Γ.comps) :=
    rv_test A σ _ fun c hc => (basB_of_plain (hFb c hc)).1
  have hdK : A.dh (σ x) β (fun ω' => Kx (cI x) Γ i₁ σ (D ω')) = fun ω' =>
      (Γ.comps.zipIdx.map fun p => A.dh (σ x) β (fun ω'' => kx (cI x) i₁ σ (D ω'') p) ω' *
        Kxq (cI x) Γ i₁ σ (D ω') p.2).sum :=
    dh_prod_rule A (σ x) β Prod.snd _ (zip_snd_nodup _) (fun p ω => kx (cI x) i₁ σ (D ω) p)
      (fun p hp => kx_test A σ hpl in_hcR i₁ hp)
  have hdF := (dTerms_spec A σ' (liftA 1 x) (newA 0) _ (plain_bas_lift hFb 1)).2 ω
  simp only [rv_liftCs, hσ', hβ] at hdF
  rw [show σ' (liftA 1 x) = σ x by rw [← hσ']; rfl] at hdF
  have hD : ((iDs x Γ i₁ e₁).map fun d => rv (D ω) σ' d).sum =
      Kx (cI x) Γ i₁ σ (D ω) * A.G ω (σ e₁.x) β *
        ((dTerms (liftA 1 x) (newA 0) (liftCs 1 (eraseIdxs (iXIdx x Γ) Γ.comps))).map
          fun d => rv (D ω) σ' d).sum := by
    rw [iDs, List.map_map, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun d _ => ?_)
    simp only [Function.comp_apply, rv_append, rv_liftCs, hσ', in_R4, oSx, iGw, rv_cons,
      rv_nil, mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_G A,
      Charge.apply, one_mul, mul_one, hβ]
    rw [show σ' (liftA 1 e₁.x) = σ e₁.x by rw [← hσ']; rfl]
    ring
  rw [dh_mul' A (σ x) β hKt hFt, hD, hdF, hdK]
  have hPP : ∀ p ∈ Γ.comps.zipIdx,
      -(A.dh (σ x) β (fun ω => kx (cI x) i₁ σ (D ω) p) ω) * Kxq (cI x) Γ i₁ σ (D ω) p.2 *
        rv (D ω) σ (eraseIdxs (iXIdx x Γ) Γ.comps) * A.G ω (σ e₁.x) β = _ :=
    fun p hp => in_PP A σ hpl hIP hL hp β ω
  have hsum : A.G ω (σ e₁.x) β * -((Γ.comps.zipIdx.map fun p =>
        A.dh (σ x) β (fun ω'' => kx (cI x) i₁ σ (D ω'') p) ω * Kxq (cI x) Γ i₁ σ (D ω) p.2).sum *
        rv (D ω) σ (eraseIdxs (iXIdx x Γ) Γ.comps)) =
      (Γ.comps.zipIdx.map fun p => -(A.dh (σ x) β (fun ω => kx (cI x) i₁ σ (D ω) p) ω) *
        Kxq (cI x) Γ i₁ σ (D ω) p.2 * rv (D ω) σ (eraseIdxs (iXIdx x Γ) Γ.comps) *
        A.G ω (σ e₁.x) β).sum := by
    rw [← List.sum_map_mul_right, ← list_sum_neg, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    ring
  rw [List.map_congr_left hPP] at hsum
  simp only [List.sum_map_add] at hsum
  have h1 := sum_filter_snd Γ.comps.zipIdx (ep x .minus false) (fun j =>
    rv (D ω) σ (eraseIdxs [i₁, j] Γ.comps) *
      (A.G ω (σ e₁.x) β * star (A.G ω (σ (Γ.comps.getD j e₁).x) β)) * star (A.G ω (σ x) (σ x)))
  have h3 := sum_ite_const Γ.comps.zipIdx (fun p => ep x .plus false p && p.2 != i₁)
    (rv (D ω) σ (Γ.comps.eraseIdx i₁) * (A.G ω (σ e₁.x) β * A.G ω β (σ x)))
  rw [len_IP hIP] at h3
  rw [← edgeIdx_eq] at h1
  simp only []
  linear_combination hsum - h1 + h3

/-- Linearity of `P_x` on a sum of the shape of [I, (3.14)]. -/
private theorem P_lin3 {γ : Type*} (X : ι) (l₁ : List ℕ) (l₅ : List γ) (f₁ : ℕ → Ω → ℂ)
    (f₅ : γ → Ω → ℂ) (c₃ : ℂ) (g₃ : Ω → ℂ) (h₁ : ∀ j ∈ l₁, A.Good (f₁ j)) (h₃ : A.Good g₃)
    (h₅ : ∀ d ∈ l₅, A.Good (f₅ d)) (ω : Ω) :
    PF.P X (fun ω' => (l₁.map fun j => f₁ j ω').sum + c₃ * g₃ ω' +
        (l₅.map fun d => f₅ d ω').sum) ω =
      (l₁.map fun j => PF.P X (f₁ j) ω).sum + c₃ * PF.P X g₃ ω +
        (l₅.map fun d => PF.P X (f₅ d) ω).sum := by
  have g1 := good_listSum A l₁ h₁
  have g5 := good_listSum A l₅ h₅
  have g3 : A.Good fun ω => c₃ * g₃ ω := A.laws.good_mul _ _ (A.laws.good_const _) h₃
  have g13 : A.Good fun ω => (l₁.map fun q => f₁ q ω).sum + c₃ * g₃ ω :=
    A.laws.good_add _ _ g1 g3
  rw [P_add' A g13 g5, P_add' A g1 g3, P_cmul' A _ h₃, P_listSum' A l₁ h₁, P_listSum' A l₅ h₅]

private theorem in_Pexp (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (σ' : Atom k (n + 1) → ι) (hσ' : σ' ∘ liftA 1 = σ)
    (β : ι) (hβ : σ' (newA 0) = β) (ω : Ω) :
    PF.P (σ x) (fun ω' => A.G ω' (σ e₁.x) β * -(A.dh (σ x) β (fun ω'' =>
        Kx (cI x) Γ i₁ σ (D ω'') * rv (D ω'') σ (eraseIdxs (iXIdx x Γ) Γ.comps)) ω')) ω =
      ((Γ.edgeIdx x .minus false).map fun j => PF.P (σ x) (fun ω' =>
          rv (D ω') σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω' (σ e₁.x) β * star (A.G ω' (σ (Γ.comps.getD j e₁).x) β)) *
          star (A.G ω' (σ x) (σ x))) ω).sum +
      (is₂.length : ℂ) * PF.P (σ x) (fun ω' => rv (D ω') σ (Γ.comps.eraseIdx i₁) *
          (A.G ω' (σ e₁.x) β * A.G ω' β (σ x))) ω +
      ((iDs x Γ i₁ e₁).map fun d => PF.P (σ x) (fun ω' => rv (D ω') σ' d) ω).sum := by
  rw [P_congr' (fun ω' => in_KEY A σ hpl hIP hL σ' hσ' β hβ ω')]
  have hE : ∀ (is : List ℕ), A.Test fun ω' => rv (D ω') σ (eraseIdxs is Γ.comps) :=
    fun is => rv_test A σ _ (bas_sub hpl fun c hc => mem_eraseIdxs hc)
  have hR : A.Test fun ω' => rv (D ω') σ (Γ.comps.eraseIdx i₁) :=
    rv_test A σ _ (bas_sub hpl fun c hc => List.mem_of_mem_eraseIdx hc)
  have hFb : ∀ c ∈ eraseIdxs (iXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  refine P_lin3 A (σ x) _ _ _ _ _ _ (fun j _ => A.test_good _ ?_) (A.test_good _ ?_)
    (fun d hd => A.test_good _ ?_) ω
  · exact test_mul' A (test_mul' A (hE _) (test_mul' A (test_G A _ _)
      (test_star' A (test_G A _ _)))) (test_star' A (test_G A _ _))
  · exact test_mul' A hR (test_mul' A (test_G A _ _) (test_G A _ _))
  · obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have hd'b := ((dTerms_spec A σ' (liftA 1 x) (newA 0) _ (plain_bas_lift hFb 1)).1 d' hd').1
    refine rv_test A σ' _ fun c hc => ?_
    rcases List.mem_append.1 hc with hc | hc
    · rcases List.mem_append.1 hc with hc | hc
      · obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
        rw [basB_map]
        exact bas_sub hpl (fun c hc => mem_pickIdxs hc) c' hc'
      · exact (hd'b c hc).1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> rfl

end InDeriv

/-! ## Case (iii): the identity at one labelling, and the value of `multiEIn` -/

section InCore

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ} {x : Atom k n} {Γ : Graph k n}

/-- The identity behind [I, (3.14)] in the form of the graphs of `multiEIn`, at one labelling
`σ` of the atoms of the input graph (`τ α` labels the new atom by `α`). -/
private theorem in_core (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (hX : Γ.xdotsAt x (iXIdx x Γ) = true) (σ : Atom k n → ι)
    (τ : ι → Atom k (n + 1) → ι) (hτ1 : ∀ α, τ α ∘ liftA 1 = σ) (hτ2 : ∀ α, τ α (newA 0) = α)
    (ω : Ω) :
    Γ.coeff.eval (msc A.z) * dv (D ω) σ Γ.comps * rv (D ω) σ Γ.comps =
      ((Γ.edgeIdx x .minus false).map fun j => ∑ α, msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ (eraseIdxs [i₁, j] Γ.comps) *
          (A.G ω' (σ e₁.x) α * star (A.G ω' (σ (Γ.comps.getD j e₁).x) α)) *
          star (A.G ω' (σ x) (σ x))) ω).sum +
      ∑ α, msc A.z * Γ.coeff.eval (msc A.z) * (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps * (A.G ω' α α - msc A.z)) ω +
      ∑ α, (is₂.length : ℂ) * msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') σ (Γ.comps.eraseIdx i₁) *
          (A.G ω' (σ e₁.x) α * A.G ω' α (σ x))) ω +
      ((iDs x Γ i₁ e₁).map fun d => ∑ α, msc A.z * Γ.coeff.eval (msc A.z) *
        (dv (D ω) σ Γ.comps * (A.S (σ x) α : ℂ)) *
        PF.P (σ x) (fun ω' => rv (D ω') (τ α) d) ω).sum +
      Γ.coeff.eval (msc A.z) * dv (D ω) σ Γ.comps *
        PF.op .Q (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω := by
  set c := Γ.coeff.eval (msc A.z)
  set Det := dv (D ω) σ Γ.comps
  have hFb : ∀ c ∈ eraseIdxs (iXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  have he₁ := ep_spec x (in_e₁_ep hIP hL)
  by_cases hXY : σ x = σ e₁.x
  · have hx1 : i₁ ∈ iXIdx x Γ := by
      rw [iXIdx, hIP]
      simp
    obtain ⟨c', hc', hk, hxy⟩ := xdot_of hX hx1 hL
    rw [ite_eq_right (he₁.2.2 rfl).2] at hxy
    have h0 : Det = 0 := dv_xdot_zero (D ω) σ hc' hk hxy hXY
    simp [h0]
  have hpe : (e₁.isPlainB = true) := hpl e₁ (List.mem_of_getElem? hL)
  have hve : ∀ ω', Comp.val (D ω') σ e₁ = A.G ω' (σ e₁.x) (σ x) := by
    intro ω'
    rw [val_edge A σ hpe he₁.1, (he₁.2.2 rfl).1]
    rfl
  set K : Ω → ℂ := fun ω' => Kx (cI x) Γ i₁ σ (D ω') *
    rv (D ω') σ (eraseIdxs (iXIdx x Γ) Γ.comps) with hKdef
  have hKt : A.Test K :=
    test_mul' A (test_listProd' A _ fun p hp => kx_test A σ hpl in_hcR i₁ hp)
      (rv_test A σ _ fun c hc => (basB_of_plain (hFb c hc)).1)
  have hR1 : ∀ ω', rv (D ω') σ Γ.comps = A.G ω' (σ e₁.x) (σ x) * K ω' := by
    intro ω'
    rw [in_R1 σ hIP hL, hve]
  have hP : PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω =
      msc A.z * ∑ β, (A.S (σ x) β : ℂ) *
        PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps * (A.G ω' β β - msc A.z)) ω +
      msc A.z * ∑ β, (A.S (σ x) β : ℂ) * PF.P (σ x) (fun ω' => A.G ω' (σ e₁.x) β *
        -(A.dh (σ x) β K ω')) ω := by
    rw [P_congr' hR1, ibp_col A (σ x) (σ e₁.x) hKt ω, ite_eq_right (Ne.symm hXY)]
    have h1 : ∀ β, PF.P (σ x) (fun ω' => (A.G ω' β β - msc A.z) * A.G ω' (σ e₁.x) (σ x) *
        K ω') ω = PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps * (A.G ω' β β - msc A.z)) ω :=
      fun β => by
        rw [P_congr' (g := fun ω' => rv (D ω') σ Γ.comps * (A.G ω' β β - msc A.z))
          fun ω' => by rw [hR1]; ring]
    have h2 : ∀ β, PF.P (σ x) (fun ω' => A.G ω' (σ e₁.x) β * A.dh (σ x) β K ω') ω =
        -PF.P (σ x) (fun ω' => A.G ω' (σ e₁.x) β * -(A.dh (σ x) β K ω')) ω := fun β => by
      rw [← P_neg' A (A.test_good _ (test_mul' A (test_G A _ _)
        (test_neg' A (test_dh' A _ _ hKt))))]
      rw [P_congr' (g := fun ω' => -(A.G ω' (σ e₁.x) β * -(A.dh (σ x) β K ω'))) fun ω' => by
        ring]
    simp only [h1, h2]
    simp only [mul_neg, Finset.sum_neg_distrib]
    ring
  rw [show rv (D ω) σ Γ.comps = PF.op .Q (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω +
    PF.P (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω by rw [Q_apply']; ring, hP]
  simp only [hKdef, fun β => in_Pexp A σ hpl hIP hL (τ β) (hτ1 β) β (hτ2 β) ω]
  rw [list_finset_comm, list_finset_comm]
  simp only [List.sum_map_mul_left, ← Finset.sum_add_distrib]
  rw [add_comm _ (c * Det * PF.op .Q (σ x) (fun ω' => rv (D ω') σ Γ.comps) ω), mul_add]
  simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

include A in
/-- Case (iii) of [I, Def 3.11]: the formal sum of `multiEIn` has the value of the graph. -/
private theorem multiEIn_valR (x : Atom k n) (Γ : Graph k n)
    (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {E : TExpansion k n} (hE : multiEIn x Γ = some E)
    (e : Fin k → ι) (ω : Ω) : S PF D e ω E = Γ.valR PF D e ω := by
  obtain ⟨i₁, is₂, e₁, hIP, hL, hX, rfl⟩ := multiEIn_some x Γ hE
  have hU : Unl Γ.comps := plain_Unl hpl
  have hr : ∃ c ∈ Γ.comps, c.kind.isRandom = true :=
    ⟨e₁, List.mem_of_getElem? hL, by rw [(ep_spec x (in_e₁_ep hIP hL)).1]; rfl⟩
  unfold iOut
  simp only [S_append, S_map_t1, S_t1, S_t0, S_ite, ite_sum]
  rw [valR_T0, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hdj : ∀ j ∈ Γ.edgeIdx x .minus false,
      dv (D ω) (Sum.elim e s) (eraseIdxs [i₁, j] Γ.comps) = dv (D ω) (Sum.elim e s) Γ.comps := by
    intro j hj
    rw [edgeIdx_eq] at hj
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hj
    exact in_D3 _ hIP hL (D ω) (List.mem_filter.1 hq).1 (by simp [cI, (List.mem_filter.1 hq).2])
  have hdE := in_D1 (Sum.elim e s) hIP hL (D ω)
  have hFb : ∀ c ∈ eraseIdxs (iXIdx x Γ) Γ.comps, c.isPlainB = true :=
    fun c hc => hpl c (mem_eraseIdxs hc)
  have hdD : ∀ d ∈ iDs x Γ i₁ e₁, ∀ α, dv (D ω) (Sum.elim e (Fin.append s ![α])) d =
      dv (D ω) (Sum.elim e s) Γ.comps * (A.S (Sum.elim e s x) α : ℂ) := by
    intro d hd α
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have h2 := ((dTerms_spec A (Sum.elim e (Fin.append s ![α])) (liftA 1 x) (newA 0) _
      (plain_bas_lift hFb 1)).1 d' hd').2 (D ω)
    rw [dv_liftCs, elim_append_comp_liftA, in_D4] at h2
    simp only [dv_append, dv_liftCs, elim_append_comp_liftA, in_D5, h2, oSx, iGw, dv_cons,
      dv_nil, mkC_kind, Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, val_s A,
      elim_append_liftA, elim_append_newA, Matrix.cons_val_zero]
    ring
  have hM := triple_sum _ _ _ _ _ fun j (hj : j ∈ Γ.edgeIdx x .minus false) =>
    (in_BM A x Γ i₁ e₁ e ω hU j s).trans (by rw [hdj j hj])
  have hL3 := out_BL A x Γ e ω hU s
  have hE1 := in_BE1 A x Γ i₁ e₁ e ω hU (is₂.isEmpty = true) is₂.length
    (fun h => by simpa using h) s
  rw [hdE] at hE1
  have hD := (in_BD A x Γ i₁ e₁ e ω hpl s).trans (congrArg List.sum (List.map_congr_left
    fun d hd => Finset.sum_congr rfl fun α _ => by rw [hdD d hd α]))
  have hQ := out_BQ A x Γ e ω hU hr s
  have hΓ := T0_self A Γ e ω hU s
  have hcore := in_core A hpl hIP hL hX (Sum.elim e s) (fun α => Sum.elim e (Fin.append s ![α]))
    (fun α => elim_append_comp_liftA e s ![α]) (fun α => by simp) ω
  linear_combination hM + hL3 + hE1 + hD + hQ - hΓ - hcore

end InCore

/-! ## The graphs of the `GG` expansion -/

section GGDefs

variable {k n : ℕ} (x : Atom k n) (Γ : Graph k n) (i j : ℕ) (e e' : Comp (Atom k n))

/-- The components other than `G_{xy}` and `G_{y'x}`. -/
private def ggF : List (Comp (Atom k n)) := eraseIdxs [i, j] Γ.comps

/-- The components other than `G_{xy}` and `G_{y'x}`, and `G_{y'y}` (the weight `G_{yy}` when
`y' = y`). -/
private def ggMain : List (Comp (Atom k n)) := ggF Γ i j ++ [solidC .plus e'.x e.y]

/-- The derivative terms of [I, (3.17)] at `α = x`: one graph of `-∂_{h_{βx}}` of the components
other than `G_{xy}` and `G_{y'x}`, and `G_{βy} G_{y'x}`. -/
private def ggD1 : List (List (Comp (Atom k (n + 1)))) :=
  (dTerms (newA 0) (liftA 1 x) (liftCs 1 (ggF Γ i j))).map fun d =>
    d ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)]

/-- The derivative terms of [I, (3.17)] at a new atom `α`: one graph of `-∂_{h_{βα}}` of the
components other than `G_{xy}` and `G_{y'x}`, and `G_{βy} G_{y'α}`. -/
private def ggD2 : List (List (Comp (Atom k (n + 2)))) :=
  (dTerms (newA 1) (newA 0) (liftCs 2 (ggF Γ i j))).map fun d =>
    d ++ [mkC (.G .plus) (newA 1) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 0)]

/-- The formal sum of `ggPos`. -/
private def ggOut : TExpansion k n :=
  let a₁ : Atom k (n + 1) := newA 0
  let a₂ : Atom k (n + 2) := newA 0
  let b₂ : Atom k (n + 2) := newA 1
  [⟨n, ⟨ggMain Γ i j e e' ++ [mkC (.waved .plus) x e.y], cm * Γ.coeff⟩, id⟩,
    t1 (liftCs 1 Γ.comps ++ [mkC (.waved .s) (liftA 1 x) a₁, mkC (.light .plus) a₁ a₁])
      (cm * Γ.coeff),
    t2 (liftCs 2 (ggF Γ i j) ++ [mkC (.waved .plus) (liftA 2 x) a₂, mkC (.waved .s) a₂ b₂,
      mkC (.light .plus) b₂ b₂, mkC (.G .plus) a₂ (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) a₂]) (cm * Γ.coeff),
    t1 (liftCs 1 (ggF Γ i j) ++ [mkC (.light .plus) (liftA 1 x) (liftA 1 x),
      mkC (.waved .s) (liftA 1 x) a₁, mkC (.G .plus) a₁ (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) a₁]) (cm * Γ.coeff),
    t2 (liftCs 2 (ggF Γ i j) ++ [mkC (.waved .plus) (liftA 2 x) a₂, mkC (.waved .s) a₂ b₂,
      mkC (.light .plus) a₂ a₂, mkC (.G .plus) b₂ (liftA 2 e.y),
      mkC (.G .plus) (liftA 2 e'.x) b₂]) (cm * Γ.coeff)] ++
    (ggD1 x Γ i j e e').map (fun d => t1 (d ++ [mkC (.waved .s) (liftA 1 x) a₁]) (cm * Γ.coeff)) ++
    (ggD2 Γ i j e e').map (fun d => t2 (d ++ [mkC (.waved .plus) (liftA 2 x) a₂,
      mkC (.waved .s) a₂ b₂]) (cm * Γ.coeff)) ++
    [⟨n, ⟨labelQs x Γ.comps, Γ.coeff⟩, id⟩,
      t1 (labelQs a₁ (liftCs 1 (ggF Γ i j) ++ [mkC (.G .plus) a₁ (liftA 1 e.y),
        mkC (.G .plus) (liftA 1 e'.x) a₁]) ++ [mkC (.waved .plus) (liftA 1 x) a₁]) Γ.coeff,
      ⟨n, ⟨labelQs e.y (ggMain Γ i j e e') ++ [mkC (.waved .plus) x e.y], -cm * Γ.coeff⟩, id⟩,
      t1 (labelQs (liftA 1 x) (liftCs 1 Γ.comps ++ [mkC (.light .plus) a₁ a₁]) ++
        [mkC (.waved .s) (liftA 1 x) a₁]) (-cm * Γ.coeff),
      t2 (labelQs a₂ (liftCs 2 (ggF Γ i j) ++ [mkC (.light .plus) b₂ b₂,
        mkC (.G .plus) a₂ (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) a₂]) ++
        [mkC (.waved .plus) (liftA 2 x) a₂, mkC (.waved .s) a₂ b₂]) (-cm * Γ.coeff),
      t1 (labelQs (liftA 1 x) (liftCs 1 (ggF Γ i j) ++ [mkC (.weight .plus) (liftA 1 x) (liftA 1 x),
        mkC (.G .plus) a₁ (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x) a₁]) ++
        [mkC (.waved .s) (liftA 1 x) a₁]) (-cm * Γ.coeff),
      t2 (labelQs a₂ (liftCs 2 (ggF Γ i j) ++ [mkC (.weight .plus) a₂ a₂,
        mkC (.G .plus) b₂ (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) b₂]) ++
        [mkC (.waved .plus) (liftA 2 x) a₂, mkC (.waved .s) a₂ b₂]) (-cm * Γ.coeff)] ++
    (ggD1 x Γ i j e e').map (fun d => t1 (labelQs (liftA 1 x) d ++
      [mkC (.waved .s) (liftA 1 x) a₁]) (-cm * Γ.coeff)) ++
    (ggD2 Γ i j e e').map (fun d => t2 (labelQs a₂ d ++ [mkC (.waved .plus) (liftA 2 x) a₂,
      mkC (.waved .s) a₂ b₂]) (-cm * Γ.coeff))

private theorem ggPos_some {E : TExpansion k n} (h : ggPos x Γ = some E) :
    ∃ i j e e', Γ.edgeIdx x .plus true = [i] ∧ Γ.edgeIdx x .plus false = [j] ∧
      Γ.comps[i]? = some e ∧ Γ.comps[j]? = some e' ∧ Γ.xdotsAt x [i, j] = true ∧
      E = ggOut x Γ i j e e' := by
  unfold ggPos at h
  split_ifs at h
  split at h
  · rename_i i j hi hj
    split at h
    · rename_i e e' he he'
      dsimp only at h
      rw [ite_eq_iff] at h
      rcases h with ⟨_, h⟩ | ⟨hX, h⟩
      · exact absurd h (by simp)
      refine ⟨i, j, e, e', hi, hj, he, he', by simpa using hX, ?_⟩
      exact (Option.some.inj h).symm
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end GGDefs

/-! ## The `GG` expansion: products over the components -/

section GGProd

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k n : ℕ} {x : Atom k n} {Γ : Graph k n}
  {i j : ℕ} {ea eb : Comp (Atom k n)} (σ : Atom k n → ι)
  (hi : Γ.edgeIdx x .plus true = [i]) (hj : Γ.edgeIdx x .plus false = [j])
  (hea : Γ.comps[i]? = some ea) (heb : Γ.comps[j]? = some eb)
include hi hj hea heb

omit [Fintype ι] [DecidableEq ι] hj heb in
private theorem gg_ea : ep x .plus true (ea, i) = true := by
  have h : i ∈ Γ.edgeIdx x .plus true := by rw [hi]; exact List.mem_singleton_self _
  rw [edgeIdx_eq] at h
  exact (mem_filter_snd (mem_zip_of_get hea)).1 h

omit [Fintype ι] [DecidableEq ι] hi hea in
private theorem gg_eb : ep x .plus false (eb, j) = true := by
  have h : j ∈ Γ.edgeIdx x .plus false := by rw [hj]; exact List.mem_singleton_self _
  rw [edgeIdx_eq] at h
  exact (mem_filter_snd (mem_zip_of_get heb)).1 h

omit [Fintype ι] [DecidableEq ι] in
private theorem gg_ne : i ≠ j := by
  intro h
  subst h
  have := zip_eq_of_snd (mem_zip_of_get hea) (mem_zip_of_get heb) rfl
  obtain rfl : ea = eb := congrArg Prod.fst this
  exact absurd (ep_excl x (gg_ea hi hea) (gg_eb hj heb)).2 (by simp)

private theorem gg_R (D₀ : Data ι) :
    rv D₀ σ Γ.comps = Comp.val D₀ σ ea * (Comp.val D₀ σ eb * rv D₀ σ (ggF Γ i j)) := by
  have hra := cX_random x (cX_of_ep x (gg_ea hi hea))
  have hrb := cX_random x (cX_of_ep x (gg_eb hj heb))
  have hij := gg_ne hi hj hea heb
  rw [rv_zip, ggF, eraseIdxs, rv_zfilter,
    ← prod_ite_single _ (zip_snd_nodup _) (fun p => Comp.val D₀ σ p.1) (mem_zip_of_get hea),
    ← prod_ite_single _ (zip_snd_nodup _) (fun p => Comp.val D₀ σ p.1) (mem_zip_of_get heb),
    ← List.prod_map_mul, ← List.prod_map_mul]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  by_cases h1 : p.2 = i
  · obtain rfl := zip_eq_of_snd hp (mem_zip_of_get hea) h1
    simp [hra, hij]
  by_cases h2 : p.2 = j
  · obtain rfl := zip_eq_of_snd hp (mem_zip_of_get heb) h2
    simp [hrb, Ne.symm hij]
  · simp [h1, h2]

private theorem gg_D (D₀ : Data ι) : dv D₀ σ (ggF Γ i j) = dv D₀ σ Γ.comps := by
  have hra := cX_random x (cX_of_ep x (gg_ea hi hea))
  have hrb := cX_random x (cX_of_ep x (gg_eb hj heb))
  rw [ggF, eraseIdxs, dv_zfilter, dv_zip]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  by_cases h1 : p.2 = i
  · obtain rfl := zip_eq_of_snd hp (mem_zip_of_get hea) h1
    simp [hra]
  by_cases h2 : p.2 = j
  · obtain rfl := zip_eq_of_snd hp (mem_zip_of_get heb) h2
    simp [hrb]
  · simp [h1, h2]

end GGProd

/-! ## The `GG` expansion: the graphs in pairs -/

section GGBlocks

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ} (x : Atom k n) (Γ : Graph k n) (i j : ℕ)
  (ea eb : Comp (Atom k n)) (e : Fin k → ι) (ω : Ω)

private theorem Unl_ggF (hU : Unl Γ.comps) : Unl (ggF Γ i j) :=
  Unl_sub hU fun _ hc => mem_eraseIdxs hc

private theorem gg_B1 (hU : Unl Γ.comps) (s : Fin n → ι) :
    T0 PF D e ω ⟨ggMain Γ i j ea eb ++ [mkC (.waved .plus) x ea.y], cm * Γ.coeff⟩ s +
      T0 PF D e ω ⟨labelQs ea.y (ggMain Γ i j ea eb) ++ [mkC (.waved .plus) x ea.y],
        -cm * Γ.coeff⟩ s =
    msc A.z * Γ.coeff.eval (msc A.z) * dv (D ω) (Sum.elim e s) (ggF Γ i j) *
      (D ω).Sp (Sum.elim e s x) (Sum.elim e s ea.y) *
      PF.P (Sum.elim e s ea.y) (fun ω' => rv (D ω') (Sum.elim e s) (ggF Γ i j) *
        A.G ω' (Sum.elim e s eb.x) (Sum.elim e s ea.y)) ω := by
  have hsol : (solidC .plus eb.x ea.y).kind.isRandom = true ∧
      (solidC .plus eb.x ea.y).label = none := by
    unfold solidC
    split_ifs <;> exact ⟨rfl, rfl⟩
  have hUM : Unl (ggMain Γ i j ea eb) :=
    Unl_append.2 ⟨Unl_ggF Γ i j hU, by simp [Unl, hsol.2]⟩
  rw [T0, T0, termR_pair (PF := PF) (D := D) ea.y _ [mkC (.waved .plus) x ea.y] _ _ _ hUM
    (by simp [Unl, mkC]) (Unl_append.2 ⟨hUM, by simp [Unl, mkC]⟩)
    ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hsol.1⟩
    (fun z => by simp only [ceval_mul, ceval_neg, ceval_cm]; ring)
    (fun D₀ σ₀ => by simp)]
  have hrv : ∀ ω', rv (D ω') (Sum.elim e s) (ggMain Γ i j ea eb) =
      rv (D ω') (Sum.elim e s) (ggF Γ i j) * A.G ω' (Sum.elim e s eb.x) (Sum.elim e s ea.y) := by
    intro ω'
    simp only [ggMain, rv_append, rv_cons, rv_nil, hsol.1, ite_true, mul_one, val_solid A,
      Charge.apply]
  have hdv : dv (D ω) (Sum.elim e s) (ggMain Γ i j ea eb) =
      dv (D ω) (Sum.elim e s) (ggF Γ i j) := by
    simp only [ggMain, dv_append, dv_cons, dv_nil, hsol.1, ite_true, mul_one]
  rw [P_congr' hrv, hdv, m_eq A, ceval_mul, ceval_cm]
  simp only [pv_cons, pv_nil, mul_one, val_Sp]

private theorem gg_B2 (hU : Unl Γ.comps) (s : Fin n → ι) :
    T1 PF D e ω ⟨liftCs 1 Γ.comps ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
        mkC (.light .plus) (newA 0) (newA 0)], cm * Γ.coeff⟩ s +
      T1 PF D e ω ⟨labelQs (liftA 1 x) (liftCs 1 Γ.comps ++
        [mkC (.light .plus) (newA 0) (newA 0)]) ++ [mkC (.waved .s) (liftA 1 x) (newA 0)],
        -cm * Γ.coeff⟩ s =
    ∑ β, msc A.z * Γ.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) Γ.comps * (A.S (Sum.elim e s x) β : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) Γ.comps *
        (A.G ω' β β - msc A.z)) ω := by
  simp only [T1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hUc : Unl (liftCs 1 Γ.comps ++ [mkC (.light .plus) (newA 0) (newA 0)]) :=
    Unl_append.2 ⟨Unl_liftCs 1 hU, by simp [Unl, mkC]⟩
  rw [termR_pair (PF := PF) (D := D) (liftA 1 x) _ [mkC (.waved .s) (liftA 1 x) (newA 0)] _ _ _
    hUc (by simp [Unl, mkC]) (Unl_append.2 ⟨Unl_liftCs 1 hU, by simp [Unl, mkC]⟩)
    ⟨mkC (.light .plus) (newA 0) (newA 0), List.mem_append_right _ (by simp), rfl⟩
    (fun z => by simp only [ceval_mul, ceval_neg, ceval_cm]; ring)
    (fun D₀ σ₀ => by simp; ring)]
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![β]))
      (liftCs 1 Γ.comps ++ [mkC (.light .plus) (newA 0) (newA 0)]) =
      rv (D ω') (Sum.elim e s) Γ.comps * (A.G ω' β β - msc A.z) := by
    intro ω'
    simp only [rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil, mkC_kind,
      Kind.isRandom, ite_true, mul_one, val_light A, elim_append_newA, Matrix.cons_val_zero,
      Charge.apply]
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![β]))
      (liftCs 1 Γ.comps ++ [mkC (.light .plus) (newA 0) (newA 0)]) =
      dv (D ω) (Sum.elim e s) Γ.comps := by
    simp only [dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil, mkC_kind,
      Kind.isRandom, ite_true, mul_one]
  rw [P_congr' hrv, hdv, elim_append_liftA, m_eq A, ceval_mul, ceval_cm]
  simp only [pv_cons, pv_nil, mul_one, val_s A, elim_append_liftA, elim_append_newA,
    Matrix.cons_val_zero]
  ring

private theorem gg_B3 (hU : Unl Γ.comps) (s : Fin n → ι) :
    T2 PF D e ω ⟨liftCs 2 (ggF Γ i j) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 1) (newA 1),
        mkC (.G .plus) (newA 0) (liftA 2 ea.y), mkC (.G .plus) (liftA 2 eb.x) (newA 0)],
        cm * Γ.coeff⟩ s +
      T2 PF D e ω ⟨labelQs (newA 0) (liftCs 2 (ggF Γ i j) ++
        [mkC (.light .plus) (newA 1) (newA 1), mkC (.G .plus) (newA 0) (liftA 2 ea.y),
          mkC (.G .plus) (liftA 2 eb.x) (newA 0)]) ++
        [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)],
        -cm * Γ.coeff⟩ s =
    ∑ α, ∑ β, msc A.z * Γ.coeff.eval (msc A.z) * (dv (D ω) (Sum.elim e s) (ggF Γ i j) *
      ((D ω).Sp (Sum.elim e s x) α * (A.S α β : ℂ))) *
      PF.P α (fun ω' => rv (D ω') (Sum.elim e s) (ggF Γ i j) * ((A.G ω' β β - msc A.z) *
        (A.G ω' α (Sum.elim e s ea.y) * A.G ω' (Sum.elim e s eb.x) α))) ω := by
  simp only [T2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  have hUc : Unl (liftCs 2 (ggF Γ i j) ++ [mkC (.light .plus) (newA 1) (newA 1),
      mkC (.G .plus) (newA 0) (liftA 2 ea.y), mkC (.G .plus) (liftA 2 eb.x) (newA 0)]) :=
    Unl_append.2 ⟨Unl_liftCs 2 (Unl_ggF Γ i j hU), by simp [Unl, mkC]⟩
  rw [termR_pair (PF := PF) (D := D) (newA 0) _ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)] _ _ _ hUc (by simp [Unl, mkC])
    (Unl_append.2 ⟨Unl_liftCs 2 (Unl_ggF Γ i j hU), by simp [Unl, mkC]⟩)
    ⟨mkC (.light .plus) (newA 1) (newA 1), List.mem_append_right _ (by simp), rfl⟩
    (fun z => by simp only [ceval_mul, ceval_neg, ceval_cm]; ring)
    (fun D₀ σ₀ => by simp; ring)]
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α, β]))
      (liftCs 2 (ggF Γ i j) ++ [mkC (.light .plus) (newA 1) (newA 1),
        mkC (.G .plus) (newA 0) (liftA 2 ea.y), mkC (.G .plus) (liftA 2 eb.x) (newA 0)]) =
      rv (D ω') (Sum.elim e s) (ggF Γ i j) * ((A.G ω' β β - msc A.z) *
        (A.G ω' α (Sum.elim e s ea.y) * A.G ω' (Sum.elim e s eb.x) α)) := by
    intro ω'
    simp only [rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil, mkC_kind,
      Kind.isRandom, ite_true, mul_one, val_light A, val_G A, elim_append_newA,
      elim_append_liftA, Matrix.cons_val_zero, Matrix.cons_val_one, 
      Charge.apply]
  have hdv : dv (D ω) (Sum.elim e (Fin.append s ![α, β]))
      (liftCs 2 (ggF Γ i j) ++ [mkC (.light .plus) (newA 1) (newA 1),
        mkC (.G .plus) (newA 0) (liftA 2 ea.y), mkC (.G .plus) (liftA 2 eb.x) (newA 0)]) =
      dv (D ω) (Sum.elim e s) (ggF Γ i j) := by
    simp only [dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil, mkC_kind,
      Kind.isRandom, ite_true, mul_one]
  rw [P_congr' hrv, hdv, elim_append_newA, m_eq A, ceval_mul, ceval_cm]
  simp only [pv_cons, pv_nil, mul_one, val_s A, val_Sp, elim_append_liftA, elim_append_newA,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private theorem gg_B4 (hU : Unl Γ.comps) (s : Fin n → ι) :
    T1 PF D e ω ⟨liftCs 1 (ggF Γ i j) ++ [mkC (.light .plus) (liftA 1 x) (liftA 1 x),
        mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 ea.y),
        mkC (.G .plus) (liftA 1 eb.x) (newA 0)], cm * Γ.coeff⟩ s +
      T1 PF D e ω ⟨labelQs (liftA 1 x) (liftCs 1 (ggF Γ i j) ++
        [mkC (.weight .plus) (liftA 1 x) (liftA 1 x), mkC (.G .plus) (newA 0) (liftA 1 ea.y),
          mkC (.G .plus) (liftA 1 eb.x) (newA 0)]) ++ [mkC (.waved .s) (liftA 1 x) (newA 0)],
        -cm * Γ.coeff⟩ s =
    ∑ β, msc A.z * Γ.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e s) (ggF Γ i j) * (A.S (Sum.elim e s x) β : ℂ)) *
      (rv (D ω) (Sum.elim e s) (ggF Γ i j) *
          ((A.G ω (Sum.elim e s x) (Sum.elim e s x) - msc A.z) *
            (A.G ω β (Sum.elim e s ea.y) * A.G ω (Sum.elim e s eb.x) β)) -
        PF.op .Q (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e s) (ggF Γ i j) *
          (A.G ω' (Sum.elim e s x) (Sum.elim e s x) *
            (A.G ω' β (Sum.elim e s ea.y) * A.G ω' (Sum.elim e s eb.x) β))) ω) := by
  simp only [T1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hUa : Unl (liftCs 1 (ggF Γ i j) ++ [mkC (.light .plus) (liftA 1 x) (liftA 1 x),
      mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 ea.y),
      mkC (.G .plus) (liftA 1 eb.x) (newA 0)]) :=
    Unl_append.2 ⟨Unl_liftCs 1 (Unl_ggF Γ i j hU), by simp [Unl, mkC]⟩
  have hUb : Unl (liftCs 1 (ggF Γ i j) ++ [mkC (.weight .plus) (liftA 1 x) (liftA 1 x),
      mkC (.G .plus) (newA 0) (liftA 1 ea.y), mkC (.G .plus) (liftA 1 eb.x) (newA 0)]) :=
    Unl_append.2 ⟨Unl_liftCs 1 (Unl_ggF Γ i j hU), by simp [Unl, mkC]⟩
  rw [termR_unl (⟨_, cm * Γ.coeff⟩ : Graph k (n + 1)) hUa,
    termR_Q (liftA 1 x) _ _ _ hUb (by simp [mkC])
      ⟨mkC (.weight .plus) (liftA 1 x) (liftA 1 x), List.mem_append_right _ (by simp), rfl⟩]
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![β]))
      (liftCs 1 (ggF Γ i j) ++ [mkC (.weight .plus) (liftA 1 x) (liftA 1 x),
        mkC (.G .plus) (newA 0) (liftA 1 ea.y), mkC (.G .plus) (liftA 1 eb.x) (newA 0)]) =
      rv (D ω') (Sum.elim e s) (ggF Γ i j) *
        (A.G ω' (Sum.elim e s x) (Sum.elim e s x) *
          (A.G ω' β (Sum.elim e s ea.y) * A.G ω' (Sum.elim e s eb.x) β)) := by
    intro ω'
    simp only [rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil, mkC_kind,
      Kind.isRandom, ite_true, mul_one, val_weight A, val_G A, elim_append_newA,
      elim_append_liftA, Matrix.cons_val_zero, Charge.apply]
  rw [funext hrv, elim_append_liftA]
  simp only [pv_eq _ _ (liftCs 1 (ggF Γ i j) ++ _), pv_cons, pv_nil, rv_append, dv_append,
    rv_liftCs, dv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil, dv_cons, dv_nil, mkC_kind,
    Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, mul_one, one_mul, val_weight A,
    val_G A, val_s A, val_light A, elim_append_newA, elim_append_liftA, Matrix.cons_val_zero,
    Charge.apply, m_eq A, ceval_mul, ceval_cm, ceval_neg]
  ring

private theorem gg_B5 (hU : Unl Γ.comps) (s : Fin n → ι) :
    T2 PF D e ω ⟨liftCs 2 (ggF Γ i j) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
        mkC (.G .plus) (newA 1) (liftA 2 ea.y), mkC (.G .plus) (liftA 2 eb.x) (newA 1)],
        cm * Γ.coeff⟩ s +
      T2 PF D e ω ⟨labelQs (newA 0) (liftCs 2 (ggF Γ i j) ++
        [mkC (.weight .plus) (newA 0) (newA 0), mkC (.G .plus) (newA 1) (liftA 2 ea.y),
          mkC (.G .plus) (liftA 2 eb.x) (newA 1)]) ++
        [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)],
        -cm * Γ.coeff⟩ s =
    ∑ α, ∑ β, msc A.z * Γ.coeff.eval (msc A.z) * (dv (D ω) (Sum.elim e s) (ggF Γ i j) *
      ((D ω).Sp (Sum.elim e s x) α * (A.S α β : ℂ))) *
      (rv (D ω) (Sum.elim e s) (ggF Γ i j) * ((A.G ω α α - msc A.z) *
          (A.G ω β (Sum.elim e s ea.y) * A.G ω (Sum.elim e s eb.x) β)) -
        PF.op .Q α (fun ω' => rv (D ω') (Sum.elim e s) (ggF Γ i j) * (A.G ω' α α *
          (A.G ω' β (Sum.elim e s ea.y) * A.G ω' (Sum.elim e s eb.x) β))) ω) := by
  simp only [T2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  have hUa : Unl (liftCs 2 (ggF Γ i j) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
      mkC (.G .plus) (newA 1) (liftA 2 ea.y), mkC (.G .plus) (liftA 2 eb.x) (newA 1)]) :=
    Unl_append.2 ⟨Unl_liftCs 2 (Unl_ggF Γ i j hU), by simp [Unl, mkC]⟩
  have hUb : Unl (liftCs 2 (ggF Γ i j) ++ [mkC (.weight .plus) (newA 0) (newA 0),
      mkC (.G .plus) (newA 1) (liftA 2 ea.y), mkC (.G .plus) (liftA 2 eb.x) (newA 1)]) :=
    Unl_append.2 ⟨Unl_liftCs 2 (Unl_ggF Γ i j hU), by simp [Unl, mkC]⟩
  rw [termR_unl (⟨_, cm * Γ.coeff⟩ : Graph k (n + 2)) hUa,
    termR_Q (newA 0) _ _ _ hUb (by simp [mkC])
      ⟨mkC (.weight .plus) (newA 0) (newA 0), List.mem_append_right _ (by simp), rfl⟩]
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α, β]))
      (liftCs 2 (ggF Γ i j) ++ [mkC (.weight .plus) (newA 0) (newA 0),
        mkC (.G .plus) (newA 1) (liftA 2 ea.y), mkC (.G .plus) (liftA 2 eb.x) (newA 1)]) =
      rv (D ω') (Sum.elim e s) (ggF Γ i j) * (A.G ω' α α *
          (A.G ω' β (Sum.elim e s ea.y) * A.G ω' (Sum.elim e s eb.x) β)) := by
    intro ω'
    simp only [rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil, mkC_kind,
      Kind.isRandom, ite_true, mul_one, val_weight A, val_G A, elim_append_newA,
      elim_append_liftA, Matrix.cons_val_zero, Matrix.cons_val_one, 
      Charge.apply]
  rw [funext hrv, elim_append_newA]
  simp only [pv_eq _ _ (liftCs 2 (ggF Γ i j) ++ _), pv_cons, pv_nil, rv_append, dv_append,
    rv_liftCs, dv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil, dv_cons, dv_nil, mkC_kind,
    Kind.isRandom, ite_true, ite_false, Bool.false_eq_true, mul_one, one_mul, val_weight A,
    val_G A, val_s A, val_Sp, val_light A, elim_append_newA, elim_append_liftA,
    Matrix.cons_val_zero, Matrix.cons_val_one, Charge.apply, m_eq A, ceval_mul,
    ceval_cm, ceval_neg]
  ring

private theorem gg_BD1 (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) (s : Fin n → ι) :
    ((ggD1 x Γ i j ea eb).map fun d =>
        T1 PF D e ω ⟨d ++ [mkC (.waved .s) (liftA 1 x) (newA 0)], cm * Γ.coeff⟩ s).sum +
      ((ggD1 x Γ i j ea eb).map fun d => T1 PF D e ω ⟨labelQs (liftA 1 x) d ++
        [mkC (.waved .s) (liftA 1 x) (newA 0)], -cm * Γ.coeff⟩ s).sum =
    ((ggD1 x Γ i j ea eb).map fun d => ∑ β, msc A.z * Γ.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e (Fin.append s ![β])) d * (A.S (Sum.elim e s x) β : ℂ)) *
      PF.P (Sum.elim e s x) (fun ω' => rv (D ω') (Sum.elim e (Fin.append s ![β])) d) ω).sum := by
  rw [← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun d hd => ?_)
  simp only [T1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
  have hpl' : ∀ c ∈ ggF Γ i j, c.isPlainB = true := fun c hc => hpl c (mem_eraseIdxs hc)
  have hd'U := ((dTerms_spec A (Sum.elim e (Fin.append s ![β])) (newA 0) (liftA 1 x) _
    (plain_bas_lift hpl' 1)).1 d' hd').1
  have hU3 : Unl (d' ++ [mkC (.G .plus) (newA 0) (liftA 1 ea.y),
      mkC (.G .plus) (liftA 1 eb.x) (liftA 1 x)]) :=
    Unl_append.2 ⟨fun c hc => (hd'U c hc).2, by simp [Unl, mkC]⟩
  rw [termR_pair (PF := PF) (D := D) (liftA 1 x) _ [mkC (.waved .s) (liftA 1 x) (newA 0)] _ _ _
    hU3 (by simp [Unl, mkC]) (Unl_append.2 ⟨hU3, by simp [Unl, mkC]⟩)
    ⟨mkC (.G .plus) (newA 0) (liftA 1 ea.y), List.mem_append_right _ (by simp), rfl⟩
    (fun z => by simp only [ceval_mul, ceval_neg, ceval_cm]; ring)
    (fun D₀ σ₀ => by simp; ring), elim_append_liftA, m_eq A, ceval_mul, ceval_cm]
  simp only [pv_cons, pv_nil, mul_one, val_s A, elim_append_liftA, elim_append_newA,
    Matrix.cons_val_zero]
  ring

private theorem gg_BD2 (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) (s : Fin n → ι) :
    ((ggD2 Γ i j ea eb).map fun d => T2 PF D e ω ⟨d ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1)], cm * Γ.coeff⟩ s).sum +
      ((ggD2 Γ i j ea eb).map fun d => T2 PF D e ω ⟨labelQs (newA 0) d ++
        [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)],
        -cm * Γ.coeff⟩ s).sum =
    ((ggD2 Γ i j ea eb).map fun d => ∑ α, ∑ β, msc A.z * Γ.coeff.eval (msc A.z) *
      (dv (D ω) (Sum.elim e (Fin.append s ![α, β])) d *
        ((D ω).Sp (Sum.elim e s x) α * (A.S α β : ℂ))) *
      PF.P α (fun ω' => rv (D ω') (Sum.elim e (Fin.append s ![α, β])) d) ω).sum := by
  rw [← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun d hd => ?_)
  simp only [T2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
  have hpl' : ∀ c ∈ ggF Γ i j, c.isPlainB = true := fun c hc => hpl c (mem_eraseIdxs hc)
  have hd'U := ((dTerms_spec A (Sum.elim e (Fin.append s ![α, β])) (newA 1) (newA 0) _
    (plain_bas_lift hpl' 2)).1 d' hd').1
  have hU3 : Unl (d' ++ [mkC (.G .plus) (newA 1) (liftA 2 ea.y),
      mkC (.G .plus) (liftA 2 eb.x) (newA 0)]) :=
    Unl_append.2 ⟨fun c hc => (hd'U c hc).2, by simp [Unl, mkC]⟩
  rw [termR_pair (PF := PF) (D := D) (newA 0) _ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)] _ _ _ hU3 (by simp [Unl, mkC])
    (Unl_append.2 ⟨hU3, by simp [Unl, mkC]⟩)
    ⟨mkC (.G .plus) (newA 1) (liftA 2 ea.y), List.mem_append_right _ (by simp), rfl⟩
    (fun z => by simp only [ceval_mul, ceval_neg, ceval_cm]; ring)
    (fun D₀ σ₀ => by simp; ring), elim_append_newA, m_eq A, ceval_mul, ceval_cm]
  simp only [pv_cons, pv_nil, mul_one, val_s A, val_Sp, elim_append_liftA, elim_append_newA,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private theorem gg_Bq2 (hU : Unl Γ.comps) (s : Fin n → ι) :
    T1 PF D e ω ⟨labelQs (newA 0) (liftCs 1 (ggF Γ i j) ++
        [mkC (.G .plus) (newA 0) (liftA 1 ea.y), mkC (.G .plus) (liftA 1 eb.x) (newA 0)]) ++
        [mkC (.waved .plus) (liftA 1 x) (newA 0)], Γ.coeff⟩ s =
    ∑ α, Γ.coeff.eval (msc A.z) * (dv (D ω) (Sum.elim e s) (ggF Γ i j) *
      (D ω).Sp (Sum.elim e s x) α) *
      PF.op .Q α (fun ω' => rv (D ω') (Sum.elim e s) (ggF Γ i j) *
        (A.G ω' α (Sum.elim e s ea.y) * A.G ω' (Sum.elim e s eb.x) α)) ω := by
  simp only [T1]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hUb : Unl (liftCs 1 (ggF Γ i j) ++ [mkC (.G .plus) (newA 0) (liftA 1 ea.y),
      mkC (.G .plus) (liftA 1 eb.x) (newA 0)]) :=
    Unl_append.2 ⟨Unl_liftCs 1 (Unl_ggF Γ i j hU), by simp [Unl, mkC]⟩
  rw [termR_Q (newA 0) _ _ _ hUb (by simp [mkC])
      ⟨mkC (.G .plus) (newA 0) (liftA 1 ea.y), List.mem_append_right _ (by simp), rfl⟩]
  have hrv : ∀ ω', rv (D ω') (Sum.elim e (Fin.append s ![α]))
      (liftCs 1 (ggF Γ i j) ++ [mkC (.G .plus) (newA 0) (liftA 1 ea.y),
        mkC (.G .plus) (liftA 1 eb.x) (newA 0)]) =
      rv (D ω') (Sum.elim e s) (ggF Γ i j) *
        (A.G ω' α (Sum.elim e s ea.y) * A.G ω' (Sum.elim e s eb.x) α) := by
    intro ω'
    simp only [rv_append, rv_liftCs, elim_append_comp_liftA, rv_cons, rv_nil, mkC_kind,
      Kind.isRandom, ite_true, mul_one, val_G A, elim_append_newA,
      elim_append_liftA, Matrix.cons_val_zero, Charge.apply]
  rw [funext hrv, elim_append_newA]
  simp only [pv_cons, pv_nil, dv_append, dv_liftCs, elim_append_comp_liftA, dv_cons, dv_nil,
    mkC_kind, Kind.isRandom, ite_true, mul_one, val_Sp, elim_append_newA, elim_append_liftA,
    Matrix.cons_val_zero, m_eq A]
  ring

end GGBlocks

/-! ## The `GG` expansion: the identity at one labelling -/

private theorem b_split1 {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (X : ι)
    (g : ι → ℂ) : ∑ α, (1 + M) X α * g α = g X + ∑ α, M X α * g α := by
  simp only [Matrix.add_apply, Matrix.one_apply, add_mul, Finset.sum_add_distrib, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private theorem b_split2 {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (X : ι)
    (s h : ι → ι → ℂ) :
    ∑ α, ∑ β, (1 + M) X α * s α β * h α β =
      ∑ β, s X β * h X β + ∑ α, ∑ β, M X α * s α β * h α β := by
  rw [show (∑ α, ∑ β, (1 + M) X α * s α β * h α β) =
      ∑ α, (1 + M) X α * ∑ β, s α β * h α β from Finset.sum_congr rfl fun α _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun β _ => by ring, b_split1]
  congr 1
  exact Finset.sum_congr rfl fun α _ => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun β _ => by ring

section GGCore

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D)

/-- [I, (3.15)] with `b = 1 + S⁺` split as `δ + S⁺`, the `δ_{xy}` term dropped (`x ≠ y`), and
the `Q` terms combined as in [I, (3.17)]; `r₁`, `r₂` are the derivative graphs. -/
private theorem gg_core_abs (X Y Y' : ι) (hY : Y ≠ X) (hY' : Y' ≠ X) (F rvL : Ω → ℂ)
    (hF : A.Test F) (hR : ∀ ω', rvL ω' = A.G ω' X Y * (A.G ω' Y' X * F ω')) {γ₁ γ₂ : Type*}
    (l₁ : List γ₁) (l₂ : List γ₂) (r₁ : γ₁ → ι → Ω → ℂ) (r₂ : γ₂ → ι → ι → Ω → ℂ)
    (hr₁ : ∀ β ω', (l₁.map fun d => r₁ d β ω').sum =
      A.G ω' β Y * A.G ω' Y' X * -A.dh β X F ω')
    (hr₂ : ∀ α β ω', (l₂.map fun d => r₂ d α β ω').sum =
      A.G ω' β Y * A.G ω' Y' α * -A.dh β α F ω')
    (hg₁ : ∀ β, ∀ d ∈ l₁, A.Good (r₁ d β)) (hg₂ : ∀ α β, ∀ d ∈ l₂, A.Good (r₂ d α β))
    (c Det : ℂ) (ω : Ω) :
    c * Det * rvL ω =
      msc A.z * c * Det * (D ω).Sp X Y * PF.P Y (fun ω' => F ω' * A.G ω' Y' Y) ω +
      ∑ β, msc A.z * c * (Det * (A.S X β : ℂ)) *
        PF.P X (fun ω' => rvL ω' * (A.G ω' β β - msc A.z)) ω +
      ∑ α, ∑ β, msc A.z * c * (Det * ((D ω).Sp X α * (A.S α β : ℂ))) *
        PF.P α (fun ω' => F ω' * ((A.G ω' β β - msc A.z) * (A.G ω' α Y * A.G ω' Y' α))) ω +
      ∑ β, msc A.z * c * (Det * (A.S X β : ℂ)) *
        (F ω * ((A.G ω X X - msc A.z) * (A.G ω β Y * A.G ω Y' β)) -
          PF.op .Q X (fun ω' => F ω' * (A.G ω' X X * (A.G ω' β Y * A.G ω' Y' β))) ω) +
      ∑ α, ∑ β, msc A.z * c * (Det * ((D ω).Sp X α * (A.S α β : ℂ))) *
        (F ω * ((A.G ω α α - msc A.z) * (A.G ω β Y * A.G ω Y' β)) -
          PF.op .Q α (fun ω' => F ω' * (A.G ω' α α * (A.G ω' β Y * A.G ω' Y' β))) ω) +
      (l₁.map fun d => ∑ β, msc A.z * c * (Det * (A.S X β : ℂ)) * PF.P X (r₁ d β) ω).sum +
      (l₂.map fun d => ∑ α, ∑ β, msc A.z * c * (Det * ((D ω).Sp X α * (A.S α β : ℂ))) *
        PF.P α (r₂ d α β) ω).sum +
      c * Det * PF.op .Q X rvL ω +
      ∑ α, c * (Det * (D ω).Sp X α) *
        PF.op .Q α (fun ω' => F ω' * (A.G ω' α Y * A.G ω' Y' α)) ω := by
  set m := msc A.z
  have hI := ggIdentity Ω ι PF D A X Y Y' F hF hY hY' ω
  dsimp only at hI
  -- the splits `b = δ + S⁺`
  have sp1 : (1 + (D ω).Sp) X Y = (D ω).Sp X Y := by
    simp [Matrix.add_apply, Ne.symm hY]
  have sp2 := b_split2 (D ω).Sp X (fun a b => (A.S a b : ℂ)) (fun a b =>
    PF.P a (fun ω' => (A.G ω' b b - m) * A.G ω' a Y * A.G ω' Y' a * F ω') ω)
  have sp3 := b_split2 (D ω).Sp X (fun a b => (A.S a b : ℂ)) (fun a b =>
    PF.P a (fun ω' => (A.G ω' a a - m) * A.G ω' b Y * A.G ω' Y' b * F ω') ω)
  have sp4 := b_split2 (D ω).Sp X (fun a b => (A.S a b : ℂ)) (fun a b =>
    PF.P a (fun ω' => A.G ω' b Y * A.G ω' Y' a * A.dh b a F ω') ω)
  have sp5 := b_split1 (D ω).Sp X (fun a =>
    PF.op .Q a (fun ω' => A.G ω' a Y * A.G ω' Y' a * F ω') ω)
  have sp6 := b_split2 (D ω).Sp X (fun a b => (A.S a b : ℂ)) (fun a b =>
    PF.op .Q a (fun ω' => A.G ω' b Y * A.G ω' Y' b * F ω') ω)
  -- the conversions
  have gG : ∀ (a b : ι), A.Good fun ω' => A.G ω' a b := fun a b => A.test_good _ (test_G A a b)
  have c1 : PF.P Y (fun ω' => A.G ω' Y' Y * F ω') ω = PF.P Y (fun ω' => F ω' * A.G ω' Y' Y) ω :=
    by rw [P_congr' (g := fun ω' => F ω' * A.G ω' Y' Y) fun ω' => by ring]
  have c2 : ∀ β, PF.P X (fun ω' => (A.G ω' β β - m) * A.G ω' X Y * A.G ω' Y' X * F ω') ω =
      PF.P X (fun ω' => rvL ω' * (A.G ω' β β - m)) ω := fun β => by
    rw [P_congr' (g := fun ω' => rvL ω' * (A.G ω' β β - m)) fun ω' => by rw [hR]; ring]
  have c2' : ∀ α β, PF.P α (fun ω' => (A.G ω' β β - m) * A.G ω' α Y * A.G ω' Y' α * F ω') ω =
      PF.P α (fun ω' => F ω' * ((A.G ω' β β - m) * (A.G ω' α Y * A.G ω' Y' α))) ω :=
    fun α β => by
      rw [P_congr' (g := fun ω' => F ω' * ((A.G ω' β β - m) * (A.G ω' α Y * A.G ω' Y' α)))
        fun ω' => by ring]
  have c36 : ∀ α β, F ω * ((A.G ω α α - m) * (A.G ω β Y * A.G ω Y' β)) -
      PF.op .Q α (fun ω' => F ω' * (A.G ω' α α * (A.G ω' β Y * A.G ω' Y' β))) ω =
      PF.P α (fun ω' => (A.G ω' α α - m) * A.G ω' β Y * A.G ω' Y' β * F ω') ω -
        m * PF.op .Q α (fun ω' => A.G ω' β Y * A.G ω' Y' β * F ω') ω := fun α β => by
    have hT : A.Good fun ω' => A.G ω' β Y * A.G ω' Y' β * F ω' :=
      A.test_good _ (test_mul' A (test_mul' A (test_G A _ _) (test_G A _ _)) hF)
    have hGT : A.Good fun ω' => A.G ω' α α * (A.G ω' β Y * A.G ω' Y' β * F ω') :=
      A.test_good _ (test_mul' A (test_G A _ _) (test_mul' A (test_mul' A (test_G A _ _)
        (test_G A _ _)) hF))
    have hmT : A.Good fun ω' => m * (A.G ω' β Y * A.G ω' Y' β * F ω') :=
      A.laws.good_mul _ _ (A.laws.good_const _) hT
    rw [P_congr' (g := fun ω' => A.G ω' α α * (A.G ω' β Y * A.G ω' Y' β * F ω') -
        m * (A.G ω' β Y * A.G ω' Y' β * F ω')) fun ω' => by ring,
      P_sub' A hGT hmT, P_cmul' A _ hT, Q_apply', Q_apply',
      P_congr' (f := fun ω' => F ω' * (A.G ω' α α * (A.G ω' β Y * A.G ω' Y' β)))
        (g := fun ω' => A.G ω' α α * (A.G ω' β Y * A.G ω' Y' β * F ω')) fun ω' => by ring]
    ring
  have c4 : ∀ β, -PF.P X (fun ω' => A.G ω' β Y * A.G ω' Y' X * A.dh β X F ω') ω =
      (l₁.map fun d => PF.P X (r₁ d β) ω).sum := fun β => by
    rw [← P_listSum' A l₁ (hg₁ β) X ω, P_congr' (fun ω' => hr₁ β ω'),
      ← P_neg' A (A.test_good _ (test_mul' A (test_mul' A (test_G A _ _) (test_G A _ _))
        (test_dh' A _ _ hF)))]
    exact congrFun (P_congr' (fun ω' => by ring) X) ω
  have c4' : ∀ α β, -PF.P α (fun ω' => A.G ω' β Y * A.G ω' Y' α * A.dh β α F ω') ω =
      (l₂.map fun d => PF.P α (r₂ d α β) ω).sum := fun α β => by
    rw [← P_listSum' A l₂ (hg₂ α β) α ω, P_congr' (fun ω' => hr₂ α β ω'),
      ← P_neg' A (A.test_good _ (test_mul' A (test_mul' A (test_G A _ _) (test_G A _ _))
        (test_dh' A _ _ hF)))]
    exact congrFun (P_congr' (fun ω' => by ring) α) ω
  have c5 : PF.op .Q X (fun ω' => A.G ω' X Y * A.G ω' Y' X * F ω') ω = PF.op .Q X rvL ω := by
    rw [Q_apply', Q_apply', hR, P_congr' (g := rvL) fun ω' => by rw [hR]; ring]
    ring
  have c5' : ∀ α, PF.op .Q α (fun ω' => A.G ω' α Y * A.G ω' Y' α * F ω') ω =
      PF.op .Q α (fun ω' => F ω' * (A.G ω' α Y * A.G ω' Y' α)) ω := fun α => by
    rw [Q_apply', Q_apply', P_congr' (g := fun ω' => F ω' * (A.G ω' α Y * A.G ω' Y' α))
      fun ω' => by ring]
    ring
  -- the blocks
  have E1 : c * Det * (m * (1 + (D ω).Sp) X Y * PF.P Y (fun ω' => A.G ω' Y' Y * F ω') ω) =
      m * c * Det * (D ω).Sp X Y * PF.P Y (fun ω' => F ω' * A.G ω' Y' Y) ω := by
    rw [sp1, c1]
    ring
  have E2 : c * Det * (m * ∑ α, ∑ β, (1 + (D ω).Sp) X α * (A.S α β : ℂ) *
        PF.P α (fun ω' => (A.G ω' β β - m) * A.G ω' α Y * A.G ω' Y' α * F ω') ω) =
      ∑ β, m * c * (Det * (A.S X β : ℂ)) * PF.P X (fun ω' => rvL ω' * (A.G ω' β β - m)) ω +
      ∑ α, ∑ β, m * c * (Det * ((D ω).Sp X α * (A.S α β : ℂ))) *
        PF.P α (fun ω' => F ω' * ((A.G ω' β β - m) * (A.G ω' α Y * A.G ω' Y' α))) ω := by
    rw [sp2]
    simp only [c2, c2', mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun β _ => by ring
    · exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring
  have E36 : c * Det * (m * ∑ α, ∑ β, (1 + (D ω).Sp) X α * (A.S α β : ℂ) *
        PF.P α (fun ω' => (A.G ω' α α - m) * A.G ω' β Y * A.G ω' Y' β * F ω') ω -
      m ^ 2 * ∑ α, ∑ β, (1 + (D ω).Sp) X α * (A.S α β : ℂ) *
        PF.op .Q α (fun ω' => A.G ω' β Y * A.G ω' Y' β * F ω') ω) =
      ∑ β, m * c * (Det * (A.S X β : ℂ)) *
        (F ω * ((A.G ω X X - m) * (A.G ω β Y * A.G ω Y' β)) -
          PF.op .Q X (fun ω' => F ω' * (A.G ω' X X * (A.G ω' β Y * A.G ω' Y' β))) ω) +
      ∑ α, ∑ β, m * c * (Det * ((D ω).Sp X α * (A.S α β : ℂ))) *
        (F ω * ((A.G ω α α - m) * (A.G ω β Y * A.G ω Y' β)) -
          PF.op .Q α (fun ω' => F ω' * (A.G ω' α α * (A.G ω' β Y * A.G ω' Y' β))) ω) := by
    rw [sp3, sp6]
    simp only [c36, mul_sub, Finset.sum_sub_distrib]
    have k1 : c * Det * (m * ∑ β, (A.S X β : ℂ) *
        PF.P X (fun ω' => (A.G ω' X X - m) * A.G ω' β Y * A.G ω' Y' β * F ω') ω) =
        ∑ β, m * c * (Det * (A.S X β : ℂ)) *
          PF.P X (fun ω' => (A.G ω' X X - m) * A.G ω' β Y * A.G ω' Y' β * F ω') ω := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun β _ => by ring
    have k2 : c * Det * (m * ∑ α, ∑ β, (D ω).Sp X α * (A.S α β : ℂ) *
        PF.P α (fun ω' => (A.G ω' α α - m) * A.G ω' β Y * A.G ω' Y' β * F ω') ω) =
        ∑ α, ∑ β, m * c * (Det * ((D ω).Sp X α * (A.S α β : ℂ))) *
          PF.P α (fun ω' => (A.G ω' α α - m) * A.G ω' β Y * A.G ω' Y' β * F ω') ω := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ => by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun β _ => by ring
    have k3 : c * Det * (m ^ 2 * ∑ β, (A.S X β : ℂ) *
        PF.op .Q X (fun ω' => A.G ω' β Y * A.G ω' Y' β * F ω') ω) =
        ∑ β, m * c * (Det * (A.S X β : ℂ)) *
          (m * PF.op .Q X (fun ω' => A.G ω' β Y * A.G ω' Y' β * F ω') ω) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun β _ => by ring
    have k4 : c * Det * (m ^ 2 * ∑ α, ∑ β, (D ω).Sp X α * (A.S α β : ℂ) *
        PF.op .Q α (fun ω' => A.G ω' β Y * A.G ω' Y' β * F ω') ω) =
        ∑ α, ∑ β, m * c * (Det * ((D ω).Sp X α * (A.S α β : ℂ))) *
          (m * PF.op .Q α (fun ω' => A.G ω' β Y * A.G ω' Y' β * F ω') ω) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ => by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun β _ => by ring
    linear_combination k1 + k2 - k3 - k4
  have E4 : c * Det * -(m * ∑ α, ∑ β, (1 + (D ω).Sp) X α * (A.S α β : ℂ) *
        PF.P α (fun ω' => A.G ω' β Y * A.G ω' Y' α * A.dh β α F ω') ω) =
      (l₁.map fun d => ∑ β, m * c * (Det * (A.S X β : ℂ)) * PF.P X (r₁ d β) ω).sum +
      (l₂.map fun d => ∑ α, ∑ β, m * c * (Det * ((D ω).Sp X α * (A.S α β : ℂ))) *
        PF.P α (r₂ d α β) ω).sum := by
    rw [sp4]
    have k5 : (l₁.map fun d => ∑ β, m * c * (Det * (A.S X β : ℂ)) * PF.P X (r₁ d β) ω).sum =
        -(c * Det * (m * ∑ β, (A.S X β : ℂ) *
          PF.P X (fun ω' => A.G ω' β Y * A.G ω' Y' X * A.dh β X F ω') ω)) := by
      rw [list_finset_comm]
      simp only [List.sum_map_mul_left, ← c4]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun β _ => by ring
    have k6 : (l₂.map fun d => ∑ α, ∑ β, m * c * (Det * ((D ω).Sp X α * (A.S α β : ℂ))) *
        PF.P α (r₂ d α β) ω).sum =
        -(c * Det * (m * ∑ α, ∑ β, (D ω).Sp X α * (A.S α β : ℂ) *
          PF.P α (fun ω' => A.G ω' β Y * A.G ω' Y' α * A.dh β α F ω') ω)) := by
      rw [list_finset_comm]
      simp only [list_finset_comm, List.sum_map_mul_left, ← c4']
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun α _ => by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun β _ => by ring
    linear_combination -k5 - k6
  have E5 : c * Det * ∑ α, (1 + (D ω).Sp) X α *
        PF.op .Q α (fun ω' => A.G ω' α Y * A.G ω' Y' α * F ω') ω =
      c * Det * PF.op .Q X rvL ω + ∑ α, c * (Det * (D ω).Sp X α) *
        PF.op .Q α (fun ω' => F ω' * (A.G ω' α Y * A.G ω' Y' α)) ω := by
    rw [sp5, c5]
    simp only [c5', mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun α _ => by ring
  rw [hR ω]
  linear_combination (c * Det) * hI + E1 + E2 + E36 + E4 + E5

end GGCore

/-! ## The `GG` expansion: value of `ggPos` -/

section GGValue

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  (A : ModelAdm Ω ι PF D) {k n : ℕ}

include A in
/-- [I, Def 3.15]: the formal sum of `ggPos` has the value of the graph. -/
private theorem ggPos_valR (x : Atom k n) (Γ : Graph k n)
    (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {E : TExpansion k n} (hE : ggPos x Γ = some E)
    (e : Fin k → ι) (ω : Ω) : S PF D e ω E = Γ.valR PF D e ω := by
  obtain ⟨i, j, ea, eb, hi, hj, hea, heb, hX, rfl⟩ := ggPos_some x Γ hE
  have hU : Unl Γ.comps := plain_Unl hpl
  have hr : ∃ c ∈ Γ.comps, c.kind.isRandom = true :=
    ⟨ea, List.mem_of_getElem? hea, by rw [(ep_spec x (gg_ea hi hea)).1]; rfl⟩
  simp only [ggOut, S_append, S_cons_t0, S_cons_t1, S_cons_t2, S_nil, S_map_t1, S_map_t2,
    add_zero]
  rw [valR_T0]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  set σ := Sum.elim e s with hσ
  have hpF : ∀ c ∈ ggF Γ i j, c.isPlainB = true := fun c hc => hpl c (mem_eraseIdxs hc)
  have hdF := gg_D σ hi hj hea heb (D ω)
  have hd1 : ∀ d ∈ ggD1 x Γ i j ea eb, ∀ β,
      dv (D ω) (Sum.elim e (Fin.append s ![β])) d = dv (D ω) σ Γ.comps := by
    intro d hd β
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have h2 := ((dTerms_spec A (Sum.elim e (Fin.append s ![β])) (newA 0) (liftA 1 x) _
      (plain_bas_lift hpF 1)).1 d' hd').2 (D ω)
    rw [dv_liftCs, elim_append_comp_liftA, hdF] at h2
    simp only [dv_append, h2, dv_cons, dv_nil, mkC_kind, Kind.isRandom, ite_true, mul_one]
  have hd2 : ∀ d ∈ ggD2 Γ i j ea eb, ∀ α β,
      dv (D ω) (Sum.elim e (Fin.append s ![α, β])) d = dv (D ω) σ Γ.comps := by
    intro d hd α β
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have h2 := ((dTerms_spec A (Sum.elim e (Fin.append s ![α, β])) (newA 1) (newA 0) _
      (plain_bas_lift hpF 2)).1 d' hd').2 (D ω)
    rw [dv_liftCs, elim_append_comp_liftA, hdF] at h2
    simp only [dv_append, h2, dv_cons, dv_nil, mkC_kind, Kind.isRandom, ite_true, mul_one]
  have h1 := gg_B1 A x Γ i j ea eb e ω hU s
  have h2 := gg_B2 A x Γ e ω hU s
  have h3 := gg_B3 A x Γ i j ea eb e ω hU s
  have h4 := gg_B4 A x Γ i j ea eb e ω hU s
  have h5 := gg_B5 A x Γ i j ea eb e ω hU s
  have h6 := (gg_BD1 A x Γ i j ea eb e ω hpl s).trans (congrArg List.sum (List.map_congr_left
    fun d hd => Finset.sum_congr rfl fun β _ => by rw [hd1 d hd β]))
  have h7 := (gg_BD2 A x Γ i j ea eb e ω hpl s).trans (congrArg List.sum (List.map_congr_left
    fun d hd => Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by
      rw [hd2 d hd α β]))
  have h8 := out_BQ A x Γ e ω hU hr s
  have h9 := gg_Bq2 A x Γ i j ea eb e ω hU s
  have hΓ := T0_self A Γ e ω hU s
  rw [hdF] at h1 h3 h4 h5 h9
  -- `x` and `y` or `y'` with the same label: every term vanishes
  have hea' := ep_spec x (gg_ea hi hea)
  have heb' := ep_spec x (gg_eb hj heb)
  by_cases hXY : σ x = σ ea.y ∨ σ x = σ eb.x
  · have h0 : dv (D ω) σ Γ.comps = 0 := by
      rcases hXY with hXY | hXY
      · obtain ⟨c', hc', hk, hxy⟩ := xdot_of hX (List.mem_cons_self ..) hea
        rw [ite_eq_left (hea'.2.1 rfl).1] at hxy
        exact dv_xdot_zero (D ω) σ hc' hk hxy hXY
      · obtain ⟨c', hc', hk, hxy⟩ := xdot_of hX (by simp) heb
        rw [ite_eq_right (heb'.2.2 rfl).2] at hxy
        exact dv_xdot_zero (D ω) σ hc' hk hxy hXY
    rw [h0] at h1 h2 h3 h4 h5 h6 h7 h8 h9 hΓ
    simp only [zero_mul, mul_zero, Finset.sum_const_zero, List.map_const', List.sum_replicate,
      smul_zero] at h1 h2 h3 h4 h5 h6 h7 h8 h9 hΓ
    linear_combination h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9 - hΓ
  push Not at hXY
  obtain ⟨hY, hY'⟩ := hXY
  have hpa : ea.isPlainB = true := hpl ea (List.mem_of_getElem? hea)
  have hpb : eb.isPlainB = true := hpl eb (List.mem_of_getElem? heb)
  have hR : ∀ ω', rv (D ω') σ Γ.comps = A.G ω' (σ x) (σ ea.y) *
      (A.G ω' (σ eb.x) (σ x) * rv (D ω') σ (ggF Γ i j)) := by
    intro ω'
    rw [gg_R σ hi hj hea heb, val_edge A σ hpa hea'.1, val_edge A σ hpb heb'.1,
      (hea'.2.1 rfl).1, (heb'.2.2 rfl).1]
    rfl
  have hFt : A.Test fun ω' => rv (D ω') σ (ggF Γ i j) :=
    rv_test A σ _ fun c hc => (basB_of_plain (hpF c hc)).1
  have hr₁ : ∀ β ω', ((ggD1 x Γ i j ea eb).map fun d =>
      rv (D ω') (Sum.elim e (Fin.append s ![β])) d).sum =
      A.G ω' β (σ ea.y) * A.G ω' (σ eb.x) (σ x) *
        -A.dh β (σ x) (fun ω'' => rv (D ω'') σ (ggF Γ i j)) ω' := by
    intro β ω'
    have hdF' := (dTerms_spec A (Sum.elim e (Fin.append s ![β])) (newA 0) (liftA 1 x) _
      (plain_bas_lift hpF 1)).2 ω'
    simp only [rv_liftCs, elim_append_comp_liftA, elim_append_newA, elim_append_liftA,
      Matrix.cons_val_zero] at hdF'
    rw [ggD1, List.map_map, ← hdF', ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun d _ => ?_)
    simp only [Function.comp_apply, rv_append, rv_cons, rv_nil, mkC_kind, Kind.isRandom,
      ite_true, mul_one, val_G A, elim_append_newA, elim_append_liftA, Matrix.cons_val_zero,
      Charge.apply]
    ring
  have hr₂ : ∀ α β ω', ((ggD2 Γ i j ea eb).map fun d =>
      rv (D ω') (Sum.elim e (Fin.append s ![α, β])) d).sum =
      A.G ω' β (σ ea.y) * A.G ω' (σ eb.x) α *
        -A.dh β α (fun ω'' => rv (D ω'') σ (ggF Γ i j)) ω' := by
    intro α β ω'
    have hdF' := (dTerms_spec A (Sum.elim e (Fin.append s ![α, β])) (newA 1) (newA 0) _
      (plain_bas_lift hpF 2)).2 ω'
    simp only [rv_liftCs, elim_append_comp_liftA, elim_append_newA, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hdF'
    rw [ggD2, List.map_map, ← hdF', ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun d _ => ?_)
    simp only [Function.comp_apply, rv_append, rv_cons, rv_nil, mkC_kind, Kind.isRandom,
      ite_true, mul_one, val_G A, elim_append_newA, elim_append_liftA, Matrix.cons_val_zero,
      Matrix.cons_val_one, Charge.apply]
    ring
  have hg₁ : ∀ β, ∀ d ∈ ggD1 x Γ i j ea eb,
      A.Good fun ω' => rv (D ω') (Sum.elim e (Fin.append s ![β])) d := by
    intro β d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have hb := ((dTerms_spec A (Sum.elim e (Fin.append s ![β])) (newA 0) (liftA 1 x) _
      (plain_bas_lift hpF 1)).1 d' hd').1
    refine A.test_good _ (rv_test A _ _ fun c hc => ?_)
    rcases List.mem_append.1 hc with hc | hc
    · exact (hb c hc).1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> rfl
  have hg₂ : ∀ α β, ∀ d ∈ ggD2 Γ i j ea eb,
      A.Good fun ω' => rv (D ω') (Sum.elim e (Fin.append s ![α, β])) d := by
    intro α β d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    have hb := ((dTerms_spec A (Sum.elim e (Fin.append s ![α, β])) (newA 1) (newA 0) _
      (plain_bas_lift hpF 2)).1 d' hd').1
    refine A.test_good _ (rv_test A _ _ fun c hc => ?_)
    rcases List.mem_append.1 hc with hc | hc
    · exact (hb c hc).1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> rfl
  have hcore := gg_core_abs A (σ x) (σ ea.y) (σ eb.x) (Ne.symm hY) (Ne.symm hY')
    (fun ω' => rv (D ω') σ (ggF Γ i j)) (fun ω' => rv (D ω') σ Γ.comps) hFt hR
    (ggD1 x Γ i j ea eb) (ggD2 Γ i j ea eb)
    (fun d β ω' => rv (D ω') (Sum.elim e (Fin.append s ![β])) d)
    (fun d α β ω' => rv (D ω') (Sum.elim e (Fin.append s ![α, β])) d) hr₁ hr₂ hg₁ hg₂
    (Γ.coeff.eval (msc A.z)) (dv (D ω) σ Γ.comps) ω
  beta_reduce at hcore
  linear_combination h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9 - hΓ - hcore

end GGValue

/-! ## Complex conjugation -/

section Conj

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The data record with the deterministic matrices `Θ`, `Σ_o`, `Θ^{(n)}_err`, the ghost factor
and the auxiliary matrices conjugated. -/
private def conjD (D₀ : Data ι) : Data ι :=
  { D₀ with
    Theta := D₀.Theta.map star
    Sig := fun o => (D₀.Sig o).map star
    ThetaErr := fun a b => (D₀.ThetaErr a b).map star
    ghost := star D₀.ghost
    aux := fun j => (D₀.aux j).map star }

omit [Fintype ι] [DecidableEq ι] in
private theorem conjD_conjD (D₀ : Data ι) : conjD (conjD D₀) = D₀ := by
  rcases D₀ with ⟨m, Gm, S, Sp, Sm, Th, Sig, TE, gh, aux⟩
  simp only [conjD, Matrix.map_map]
  congr <;> simp [Function.comp_def]

omit [DecidableEq ι] in
private theorem chain_conjD (D₀ : Data ι) (o : List ℕ) :
    (conjD D₀).chain o = (D₀.chain o).map star := by
  unfold Data.chain
  suffices h : ∀ M : Matrix ι ι ℂ, o.foldl (fun M l => M * (conjD D₀).Sig l * (conjD D₀).Theta)
      (M.map star) = (o.foldl (fun M l => M * D₀.Sig l * D₀.Theta) M).map star by
    exact h D₀.Theta
  induction o with
  | nil => intro M; rfl
  | cons l o ih =>
    intro M
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    change M.map (starRingEnd ℂ) * (D₀.Sig l).map (starRingEnd ℂ) *
      D₀.Theta.map (starRingEnd ℂ) = (M * D₀.Sig l * D₀.Theta).map (starRingEnd ℂ)
    rw [Matrix.map_mul, Matrix.map_mul]

omit [Fintype ι] [DecidableEq ι] in
private theorem star_ofReal_mat (S : Matrix ι ι ℝ) (a b : ι) :
    star ((S.map fun r => (r : ℂ)) a b) = (S.map fun r => (r : ℂ)) a b := by
  simp [Matrix.map_apply]

/-- The factor of the conjugate component is the conjugate of the factor under `conjD`, when `S`
is real and `S⁻ = \overline{S⁺}`. -/
private theorem val_conj {V : Type*} (D₀ : Data ι) (σ : V → ι) (c : Comp V)
    (hS : ∀ a b, star (D₀.S a b) = D₀.S a b) (hSm : D₀.Sm = D₀.Sp.map star) :
    Comp.val D₀ σ { c with kind := c.kind.conj } = star (Comp.val (conjD D₀) σ c) := by
  rcases c with ⟨κ, x, y, mi, l⟩
  have hfl : ∀ (ch : Charge) (w : ℂ), ch.flip.apply w = star (ch.apply w) := by
    intro ch w
    cases ch <;> simp [Charge.flip, Charge.apply]
  cases κ with
  | G ch => simp only [Comp.val, Kind.conj, hfl]; rfl
  | weight ch => simp only [Comp.val, Kind.conj, hfl]; rfl
  | light ch => simp only [Comp.val, Kind.conj, hfl]; rfl
  | inv ch => simp only [Comp.val, Kind.conj, hfl]; rfl
  | wD ch d => simp only [Comp.val, Kind.conj, hfl]; rfl
  | waved w =>
    cases w
    · simp only [Comp.val, Kind.conj]
      exact (hS _ _).symm
    · simp only [Comp.val, Kind.conj, hSm, Matrix.map_apply]
      rfl
    · simp only [Comp.val, Kind.conj]
      change D₀.Sp _ _ = star (D₀.Sm _ _)
      rw [hSm, Matrix.map_apply, star_star]
  | theta o =>
    simp only [Comp.val, Kind.conj, chain_conjD, Matrix.map_apply, star_star]
  | thetaErr a b => simp [Comp.val, Kind.conj, conjD]
  | ghost => simp [Comp.val, Kind.conj, conjD]
  | aux j r b => simp [Comp.val, Kind.conj, conjD]
  | dot => simp only [Comp.val, Kind.conj]; split_ifs <;> simp
  | xdot => simp only [Comp.val, Kind.conj]; split_ifs <;> simp

private theorem CVar_conj_eval (z : ℂ) (v : CVar) :
    CVar.eval z (CVar.conj v) = star (CVar.eval z v) := by
  cases v <;> simp [CVar.conj, CVar.eval, star_inv₀]

private theorem Coeff_conj_eval (z : ℂ) (p : Coeff) :
    (Coeff.conj p).eval z = star (p.eval z) := by
  unfold Coeff.conj Coeff.eval
  rw [MvPolynomial.eval_map, MvPolynomial.eval₂_rename, Complex.star_def, MvPolynomial.eval,
    MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  congr 1
  funext v
  simp [CVar_conj_eval]

end Conj

section ConjAdm

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}

/-- The model relations hold for the data records `conjD (D ω)`. -/
private def conjAdm (A : ModelAdm Ω ι PF D) : ModelAdm Ω ι PF (fun ω => conjD (D ω)) where
  H := A.H
  z := A.z
  S := A.S
  E := A.E
  Meas := A.Meas
  Good := A.Good
  Test := A.Test
  dh := A.dh
  isHermitian := A.isHermitian
  im_pos := A.im_pos
  isSymm := A.isSymm
  nonneg := A.nonneg
  rowSum := A.rowSum
  data_m := A.data_m
  data_G := A.data_G
  data_minor := A.data_minor
  data_S := A.data_S
  data_Sp := A.data_Sp
  data_Sm := A.data_Sm
  data_Theta := fun ω => by
    have h := congrArg (fun M : Matrix ι ι ℂ => M.map (starRingEnd ℂ)) (A.data_Theta ω)
    simp only [Matrix.map_mul] at h
    have hr : ∀ M : Matrix ι ι ℂ, (∀ a b, star (M a b) = M a b) → M.map (starRingEnd ℂ) = M :=
      fun M hM => by ext a b; exact hM a b
    have h1 : ∀ a b, star ((((‖msc A.z‖ ^ 2 : ℝ) : ℂ) • (D ω).S) a b) =
        (((‖msc A.z‖ ^ 2 : ℝ) : ℂ) • (D ω).S) a b := by
      intro a b
      simp [A.data_S, Matrix.map_apply]
    have h2 : ∀ a b, star ((1 - ((‖msc A.z‖ ^ 2 : ℝ) : ℂ) • (D ω).S) a b) =
        (1 - ((‖msc A.z‖ ^ 2 : ℝ) : ℂ) • (D ω).S) a b := by
      intro a b
      rw [Matrix.sub_apply, star_sub, h1, Matrix.one_apply]
      split_ifs <;> simp
    rw [hr _ h1, hr _ h2] at h
    exact h
  laws := A.laws
  meas_add := A.meas_add
  meas_mul := A.meas_mul
  meas_minor := A.meas_minor
  P_star := A.P_star
  good_star := A.good_star
  good_entry := A.good_entry
  good_inv := A.good_inv
  good_H := A.good_H
  test_good := A.test_good
  test_const := A.test_const
  test_add := A.test_add
  test_mul := A.test_mul
  test_star := A.test_star
  test_entry := A.test_entry
  test_dh := A.test_dh
  dh_add := A.dh_add
  dh_mul := A.dh_mul
  dh_const := A.dh_const
  dh_green := A.dh_green
  dh_conj_green := A.dh_conj_green
  ibp := A.ibp

omit [Fintype ι] [DecidableEq ι] in
private theorem conjD_conjD' : (fun ω => conjD (conjD (D ω))) = D := funext fun _ => conjD_conjD _

private theorem val_conjD_random {V : Type*} (D₀ : Data ι) (σ : V → ι) (c : Comp V)
    (h : c.kind.isRandom = true) : Comp.val (conjD D₀) σ c = Comp.val D₀ σ c := by
  rcases c with ⟨κ, x, y, mi, l⟩
  cases κ <;> first | rfl | simp [Kind.isRandom] at h

/-- Components without label, or random components without minor that are not `(G_{xx})⁻¹` or
`W_D` weights. -/
private def OK {V : Type*} (cs : List (Comp V)) : Prop :=
  ∀ c ∈ cs, c.label = none ∨ (c.kind.isRandom = true ∧ basB c = true)

/-- The term of the conjugate graph is the conjugate of the term under `conjD`. -/
private theorem termR_conj (A : ModelAdm Ω ι PF D) {k N : ℕ} (g : Graph k N) (hok : OK g.comps)
    (σ : Atom k N → ι) (ω : Ω) :
    g.conj.termR PF D σ ω = star (g.termR PF (fun ω => conjD (D ω)) σ ω) := by
  have hS : ∀ ω a b, star ((D ω).S a b) = (D ω).S a b := fun ω a b => by
    rw [A.data_S]; exact star_ofReal_mat _ a b
  have hc : ∀ ω (c : Comp (Atom k N)), Comp.val (D ω) σ { c with kind := c.kind.conj } =
      star (Comp.val (conjD (D ω)) σ c) := fun ω c => val_conj _ σ c (hS ω) (A.data_Sm ω)
  have hlab : g.conj.labels = g.labels := by
    unfold Graph.labels Graph.conj
    rw [List.filterMap_map]
    rfl
  have hprod : ∀ (ω : Ω) (p : Comp (Atom k N) → Bool), (((g.comps.map fun c =>
      { c with kind := c.kind.conj }).filter p).map (Comp.val (D ω) σ)).prod =
      star (((g.comps.filter fun c => p { c with kind := c.kind.conj }).map
        (Comp.val (conjD (D ω)) σ)).prod) := by
    intro ω p
    rw [List.filter_map, List.map_map, Complex.star_def, map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun c _ => by
      simp only [Function.comp_apply, hc, Complex.star_def])
  unfold Graph.termR
  rw [hlab]
  simp only [Graph.conj, Coeff_conj_eval] at hprod ⊢
  rw [hprod ω]
  have hop : ∀ ℓ ∈ g.labels, PF.op ℓ.1 (σ ℓ.2) (fun ω' => (((g.comps.map fun c =>
      { c with kind := c.kind.conj }).filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (D ω') σ)).prod) ω =
      star (PF.op ℓ.1 (σ ℓ.2) (fun ω' => ((g.comps.filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (conjD (D ω')) σ)).prod) ω) := by
    intro ℓ hℓ
    have hf : (fun ω' => (((g.comps.map fun c => { c with kind := c.kind.conj }).filter
        fun c => decide (c.label = some ℓ)).map (Comp.val (D ω') σ)).prod) =
        fun ω' => star (((g.comps.filter fun c => decide (c.label = some ℓ)).map
          (Comp.val (conjD (D ω')) σ)).prod) := funext fun ω' => hprod ω' _
    have hgood : A.Good fun ω' => ((g.comps.filter fun c => decide (c.label = some ℓ)).map
        (Comp.val (conjD (D ω')) σ)).prod := by
      refine A.test_good _ (test_listProd' A _ fun c hc' => ?_)
      obtain ⟨hcm, hcl⟩ := List.mem_filter.1 hc'
      rcases hok c hcm with h | ⟨hr, hb⟩
      · simp [h] at hcl
      · simp only [val_conjD_random _ σ c hr]
        exact val_test A σ c hb hr
    rw [hf]
    rcases ℓ with ⟨pq, u⟩
    cases pq
    · exact congrFun (A.P_star _ _ hgood) ω
    · simp only [PFamily.op, Pi.sub_apply, star_sub]
      rw [congrFun (A.P_star _ _ hgood) ω]
  rw [List.map_congr_left hop, Complex.star_def, map_mul, map_mul]
  simp only [map_list_prod, List.map_map, Function.comp_def]
  rfl

private theorem valR_conj (A : ModelAdm Ω ι PF D) {k N : ℕ} (g : Graph k N) (hok : OK g.comps)
    (e : Fin k → ι) (ω : Ω) :
    g.conj.valR PF D e ω = star (g.valR PF (fun ω => conjD (D ω)) e ω) := by
  simp only [Graph.valR, termR_conj A g hok, Complex.star_def, map_sum]

end ConjAdm

/-! ## Labelled components of the output graphs -/

section OKLists

/-- Components without minor and without label that are not `(G_{xx})⁻¹` or `W_D` weights. -/
private def PB {V : Type*} (cs : List (Comp V)) : Prop :=
  ∀ c ∈ cs, basB c = true ∧ c.label = none

private theorem PB_append {V : Type*} {a b : List (Comp V)} : PB (a ++ b) ↔ PB a ∧ PB b := by
  simp only [PB, List.mem_append, or_imp, forall_and]
  tauto

private theorem PB_cons {V : Type*} {c : Comp V} {cs : List (Comp V)} :
    PB (c :: cs) ↔ (basB c = true ∧ c.label = none) ∧ PB cs := by
  simp [PB]

private theorem PB_nil {V : Type*} : PB ([] : List (Comp V)) := by simp [PB]

private theorem PB_liftCs {k n : ℕ} (j : ℕ) {cs : List (Comp (Atom k n))} (h : PB cs) :
    PB (liftCs j cs) := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  exact ⟨by rw [basB_map]; exact (h c' hc').1, by simp [Comp.map, (h c' hc').2]⟩

private theorem PB_sub {V : Type*} {cs cs' : List (Comp V)} (h : PB cs)
    (hs : ∀ c ∈ cs', c ∈ cs) : PB cs' := fun c hc => h c (hs c hc)

private theorem PB_solidC {V : Type*} [DecidableEq V] (ch : Charge) (u v : V) :
    basB (solidC ch u v) = true ∧ (solidC ch u v).label = none := by
  unfold solidC
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem PB_of_plain {k n : ℕ} {cs : List (Comp (Atom k n))}
    (h : ∀ c ∈ cs, c.isPlainB = true) : PB cs := fun c hc => basB_of_plain (h c hc)

private theorem OK_of_PB {V : Type*} {cs : List (Comp V)} (h : PB cs) : OK cs :=
  fun c hc => Or.inl (h c hc).2

private theorem OK_labelQs {V : Type*} (u : V) {cs : List (Comp V)} (h : PB cs) :
    OK (labelQs u cs) := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  unfold Comp.labelQ
  split_ifs with hr
  · exact Or.inr ⟨hr, (h c' hc').1⟩
  · exact Or.inl (h c' hc').2

private theorem OK_append {V : Type*} {a b : List (Comp V)} (ha : OK a) (hb : OK b) :
    OK (a ++ b) := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact ha c h
  · exact hb c h

private theorem dPieces_PB {V : Type*} [DecidableEq V] (p q : V) (c : Comp V) :
    ∀ ps, c.dPieces p q = some ps → PB ps := by
  intro ps h
  rcases c with ⟨κ, x, y, mi, l⟩
  cases κ <;> try (cases ‹Charge›)
  all_goals simp only [Comp.dPieces, Option.some.injEq, reduceCtorEq] at h
  all_goals (subst h; simp only [PB_cons, PB_nil, and_true]; exact ⟨PB_solidC _ _ _,
    PB_solidC _ _ _⟩)

private theorem dTerms_PB {V : Type*} [DecidableEq V] (p q : V) {cs : List (Comp V)}
    (h : PB cs) : ∀ d ∈ dTerms p q cs, PB d := by
  induction cs with
  | nil => simp [dTerms]
  | cons c cs ih =>
    intro d hd
    rw [dTerms_cons] at hd
    rcases List.mem_append.1 hd with hd | hd
    · cases hp : c.dPieces p q with
      | none => simp [hp] at hd
      | some ps =>
        simp only [hp, Option.map_some, Option.toList_some, List.mem_singleton] at hd
        subst hd
        exact PB_append.2 ⟨fun c' hc' => h c' (List.mem_cons_of_mem _ hc'),
          dPieces_PB p q c ps hp⟩
    · obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
      exact PB_cons.2 ⟨h c (List.mem_cons_self ..),
        ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) d' hd'⟩

private theorem fa_append {k n : ℕ} {P : Tracked k n → Prop} {E₁ E₂ : TExpansion k n}
    (h₁ : ∀ t ∈ E₁, P t) (h₂ : ∀ t ∈ E₂, P t) : ∀ t ∈ E₁ ++ E₂, P t := by
  intro t ht
  rcases List.mem_append.1 ht with h | h
  · exact h₁ t h
  · exact h₂ t h

private theorem fa_map {k n : ℕ} {β : Type*} {P : Tracked k n → Prop} {l : List β}
    {f : β → Tracked k n} (h : ∀ j ∈ l, P (f j)) : ∀ t ∈ l.map f, P t := by
  intro t ht
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ht
  exact h j hj

private theorem fa_cons {k n : ℕ} {P : Tracked k n → Prop} {t : Tracked k n}
    {E : TExpansion k n} (h₁ : P t) (h₂ : ∀ t ∈ E, P t) : ∀ t' ∈ t :: E, P t' := by
  intro t' ht'
  rcases List.mem_cons.1 ht' with rfl | h
  · exact h₁
  · exact h₂ t' h

private theorem fa_nil {k n : ℕ} {P : Tracked k n → Prop} : ∀ t ∈ ([] : TExpansion k n), P t := by
  simp

private theorem fa_ite {k n : ℕ} {P : Tracked k n → Prop} {b : Prop} [Decidable b]
    {E : TExpansion k n} (h : ∀ t ∈ E, P t) : ∀ t ∈ (if b then [] else E), P t := by
  split_ifs
  · exact fa_nil
  · exact h

end OKLists

section OKOut

variable {k n : ℕ} (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ) (e₁ : Comp (Atom k n))

private theorem PB_lift_sub {j : ℕ} {cs : List (Comp (Atom k n))} (h : PB Γ.comps)
    (hs : ∀ c ∈ cs, c ∈ Γ.comps) : PB (liftCs j cs) := PB_liftCs j (PB_sub h hs)

/-- Proves `PB` of a list of explicit components. -/
local macro "pb_lit" : tactic =>
  `(tactic| repeat (first | exact PB_nil | refine PB_cons.2 ⟨⟨rfl, rfl⟩, ?_⟩))

/-- The labelled components of the graphs of `multiEOut` are random components without
minor. -/
private theorem oOut_OK (hPB : PB Γ.comps) : ∀ t ∈ oOut x Γ i₁ is₂ e₁, OK t.g.comps := by
  have hM : ∀ j, PB (oBaseM x Γ i₁ e₁ j) := fun j => PB_append.2
    ⟨PB_lift_sub Γ hPB fun _ hc => mem_eraseIdxs hc, by simp [PB, basB, mkC, oSx, oGy]⟩
  have hP : ∀ j, PB (oBaseP x Γ i₁ e₁ j) := fun j => PB_append.2
    ⟨PB_lift_sub Γ hPB fun _ hc => mem_eraseIdxs hc, by simp [PB, basB, mkC, oSx, oGy]⟩
  have hL3 : PB (oL3 x Γ) := PB_append.2 ⟨PB_liftCs 1 hPB, by simp [PB, basB, mkC, oSx]⟩
  have hE1 : PB (oE1 x Γ i₁ e₁) := PB_append.2 ⟨PB_lift_sub Γ hPB fun _ hc =>
    List.mem_of_mem_eraseIdx hc, by simp [PB, basB, mkC, oSx, oGy]⟩
  have hE2 : PB (oE2 x Γ i₁ e₁) := PB_append.2 ⟨PB_lift_sub Γ hPB fun _ hc =>
    List.mem_of_mem_eraseIdx hc, by simp [PB, basB, mkC, oSx, oGy]⟩
  have hD : ∀ d ∈ oDs x Γ i₁ e₁, PB d := by
    intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    exact PB_append.2 ⟨PB_append.2 ⟨PB_lift_sub Γ hPB fun _ hc => mem_pickIdxs hc,
      dTerms_PB _ _ (PB_lift_sub Γ hPB fun _ hc => mem_eraseIdxs hc) d' hd'⟩,
      by simp [PB, basB, mkC, oSx, oGy]⟩
  have hw : ∀ (cs : List (Comp (Atom k (n + 1)))) (κ : Kind), PB cs →
      basB (mkC κ (liftA 1 x) (liftA 1 x)) = true →
      PB (cs ++ [mkC κ (liftA 1 x) (liftA 1 x)]) := fun cs κ h hκ =>
    PB_append.2 ⟨h, PB_cons.2 ⟨⟨hκ, rfl⟩, PB_nil⟩⟩
  unfold oOut
  refine fa_append (fa_append (fa_append (fa_append (fa_append (fa_append (fa_append
    (fa_append (fa_append (fa_append (fa_append (fa_append (fa_append (fa_append
      ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact fa_map fun j _ => OK_of_PB (hM j)
  · exact fa_map fun j _ => OK_of_PB (hP j)
  · exact fa_map fun j _ => OK_of_PB (hw _ _ (hM j) rfl)
  · exact fa_map fun j _ => OK_of_PB (hw _ _ (hP j) rfl)
  · exact fa_cons (OK_of_PB hL3) fa_nil
  · exact fa_ite (fa_cons (OK_of_PB hE1) fa_nil)
  · exact fa_ite (fa_cons (OK_of_PB hE2) fa_nil)
  · exact fa_map fun d hd => OK_of_PB (hD d hd)
  · exact fa_cons (OK_labelQs x hPB) fa_nil
  · exact fa_map fun j _ => OK_labelQs _ (hw _ _ (hM j) rfl)
  · exact fa_map fun j _ => OK_labelQs _ (hw _ _ (hP j) rfl)
  · exact fa_cons (OK_labelQs _ hL3) fa_nil
  · exact fa_ite (fa_cons (OK_labelQs _ hE1) fa_nil)
  · exact fa_ite (fa_cons (OK_labelQs _ hE2) fa_nil)
  · exact fa_map fun d hd => OK_labelQs _ (hD d hd)

/-- The labelled components of the graphs of `multiEIn` are random components without
minor. -/
private theorem iOut_OK (hPB : PB Γ.comps) : ∀ t ∈ iOut x Γ i₁ is₂ e₁, OK t.g.comps := by
  have hM : ∀ j, PB (iBaseM x Γ i₁ e₁ j) := fun j => PB_append.2
    ⟨PB_lift_sub Γ hPB fun _ hc => mem_eraseIdxs hc, by simp [PB, basB, mkC, oSx, iGw]⟩
  have hL3 : PB (oL3 x Γ) := PB_append.2 ⟨PB_liftCs 1 hPB, by simp [PB, basB, mkC, oSx]⟩
  have hE1 : PB (iE1 x Γ i₁ e₁) := PB_append.2 ⟨PB_lift_sub Γ hPB fun _ hc =>
    List.mem_of_mem_eraseIdx hc, by simp [PB, basB, mkC, oSx, iGw]⟩
  have hD : ∀ d ∈ iDs x Γ i₁ e₁, PB d := by
    intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    exact PB_append.2 ⟨PB_append.2 ⟨PB_lift_sub Γ hPB fun _ hc => mem_pickIdxs hc,
      dTerms_PB _ _ (PB_lift_sub Γ hPB fun _ hc => mem_eraseIdxs hc) d' hd'⟩,
      by simp [PB, basB, mkC, oSx, iGw]⟩
  have hw : ∀ (cs : List (Comp (Atom k (n + 1)))) (κ : Kind), PB cs →
      basB (mkC κ (liftA 1 x) (liftA 1 x)) = true →
      PB (cs ++ [mkC κ (liftA 1 x) (liftA 1 x)]) := fun cs κ h hκ =>
    PB_append.2 ⟨h, PB_cons.2 ⟨⟨hκ, rfl⟩, PB_nil⟩⟩
  unfold iOut
  refine fa_append (fa_append (fa_append (fa_append (fa_append (fa_append (fa_append
    (fa_append (fa_append ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact fa_map fun j _ => OK_of_PB (hM j)
  · exact fa_map fun j _ => OK_of_PB (hw _ _ (hM j) rfl)
  · exact fa_cons (OK_of_PB hL3) fa_nil
  · exact fa_ite (fa_cons (OK_of_PB hE1) fa_nil)
  · exact fa_map fun d hd => OK_of_PB (hD d hd)
  · exact fa_cons (OK_labelQs x hPB) fa_nil
  · exact fa_map fun j _ => OK_labelQs _ (hw _ _ (hM j) rfl)
  · exact fa_cons (OK_labelQs _ hL3) fa_nil
  · exact fa_ite (fa_cons (OK_labelQs _ hE1) fa_nil)
  · exact fa_map fun d hd => OK_labelQs _ (hD d hd)

/-- The labelled components of the graphs of `ggPos` are random components without minor. -/
private theorem ggOut_OK (i j : ℕ) (ea eb : Comp (Atom k n)) (hPB : PB Γ.comps) :
    ∀ t ∈ ggOut x Γ i j ea eb, OK t.g.comps := by
  have hF1 : PB (liftCs 1 (ggF Γ i j)) := PB_lift_sub Γ hPB fun _ hc => mem_eraseIdxs hc
  have hF2 : PB (liftCs 2 (ggF Γ i j)) := PB_lift_sub Γ hPB fun _ hc => mem_eraseIdxs hc
  have hMain : PB (ggMain Γ i j ea eb) := PB_append.2 ⟨PB_sub hPB fun _ hc => mem_eraseIdxs hc,
    PB_cons.2 ⟨PB_solidC _ _ _, PB_nil⟩⟩
  have hD1 : ∀ d ∈ ggD1 x Γ i j ea eb, PB d := by
    intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    exact PB_append.2 ⟨dTerms_PB _ _ hF1 d' hd', by pb_lit⟩
  have hD2 : ∀ d ∈ ggD2 Γ i j ea eb, PB d := by
    intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    exact PB_append.2 ⟨dTerms_PB _ _ hF2 d' hd', by pb_lit⟩
  unfold ggOut
  refine fa_append (fa_append (fa_append (fa_append (fa_append ?_ ?_) ?_) ?_) ?_) ?_
  · refine fa_cons ?_ (fa_cons ?_ (fa_cons ?_ (fa_cons ?_ (fa_cons ?_ fa_nil))))
    · exact OK_of_PB (PB_append.2 ⟨hMain, by pb_lit⟩)
    · exact OK_of_PB (PB_append.2 ⟨PB_liftCs 1 hPB, by pb_lit⟩)
    · exact OK_of_PB (PB_append.2 ⟨hF2, by pb_lit⟩)
    · exact OK_of_PB (PB_append.2 ⟨hF1, by pb_lit⟩)
    · exact OK_of_PB (PB_append.2 ⟨hF2, by pb_lit⟩)
  · exact fa_map fun d hd => OK_of_PB (PB_append.2 ⟨hD1 d hd, by pb_lit⟩)
  · exact fa_map fun d hd => OK_of_PB (PB_append.2 ⟨hD2 d hd, by pb_lit⟩)
  · refine fa_cons ?_ (fa_cons ?_ (fa_cons ?_ (fa_cons ?_ (fa_cons ?_ (fa_cons ?_
      (fa_cons ?_ fa_nil))))))
    · exact OK_labelQs x hPB
    · exact OK_append (OK_labelQs _ (PB_append.2 ⟨hF1, by pb_lit⟩))
        (OK_of_PB (by pb_lit))
    · exact OK_append (OK_labelQs _ hMain) (OK_of_PB (by pb_lit))
    · exact OK_append (OK_labelQs _ (PB_append.2 ⟨PB_liftCs 1 hPB, by pb_lit⟩))
        (OK_of_PB (by pb_lit))
    · exact OK_append (OK_labelQs _ (PB_append.2 ⟨hF2, by pb_lit⟩))
        (OK_of_PB (by pb_lit))
    · exact OK_append (OK_labelQs _ (PB_append.2 ⟨hF1, by pb_lit⟩))
        (OK_of_PB (by pb_lit))
    · exact OK_append (OK_labelQs _ (PB_append.2 ⟨hF2, by pb_lit⟩))
        (OK_of_PB (by pb_lit))
  · exact fa_map fun d hd => OK_append (OK_labelQs _ (hD1 d hd)) (OK_of_PB (by
      pb_lit))
  · exact fa_map fun d hd => OK_append (OK_labelQs _ (hD2 d hd)) (OK_of_PB (by
      pb_lit))

end OKOut

/-! ## Value preservation -/

section Assembly

variable {Ω ι : Type} [Fintype ι] [DecidableEq ι] {PF : PFamily Ω ι} {D : Ω → Data ι}
  {k n : ℕ}

private theorem conj_plain {Γ : Graph k n} (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) :
    ∀ c ∈ Γ.conj.comps, c.isPlainB = true := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  have h := hpl c' hc'
  rcases c' with ⟨κ, x, y, mi, l⟩
  cases κ <;> try (cases ‹Charge›)
  all_goals first | exact h | (cases ‹Wave› <;> exact h)

private theorem S_conj (A : ModelAdm Ω ι PF D) (E : TExpansion k n)
    (hok : ∀ t ∈ E, OK t.g.comps) (e : Fin k → ι) (ω : Ω) :
    S PF D e ω E.conj = star (S PF (fun ω => conjD (D ω)) e ω E) := by
  induction E with
  | nil => simp [TExpansion.conj, S_nil]
  | cons t E ih =>
    have h1 := hok t (List.mem_cons_self ..)
    have h2 := ih fun t' ht' => hok t' (List.mem_cons_of_mem _ ht')
    simp only [TExpansion.conj, List.map_cons] at h2 ⊢
    rw [S_cons, S_cons, h2, valR_conj A t.g h1, star_add]

private theorem valR_eq_star (A : ModelAdm Ω ι PF D) (Γ : Graph k n)
    (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) (e : Fin k → ι) (ω : Ω) :
    Γ.valR PF D e ω = star (Γ.conj.valR PF (fun ω => conjD (D ω)) e ω) := by
  have h := valR_conj (conjAdm A) Γ (OK_of_PB (PB_of_plain hpl)) e ω
  rw [conjD_conjD'] at h
  rw [h, star_star]

/-- `O_dot` applied to every graph of a tracked formal sum keeps its value. -/
private theorem S_bind_oDot (E : TExpansion k n) (e : Fin k → ι) (ω : Ω) :
    S PF D e ω (E.bind fun _ g => oDotT g) = S PF D e ω E := by
  induction E with
  | nil => rfl
  | cons t E ih =>
    have hb : TExpansion.bind (t :: E) (fun _ g => oDotT g) =
        (oDotT t.g).map (fun s => (⟨s.nOut, s.g, s.f ∘ t.f⟩ : Tracked k n)) ++
          TExpansion.bind E fun _ g => oDotT g := by
      simp [TExpansion.bind, List.flatMap_cons]
    rw [hb, S_append, ih, S_cons]
    congr 1
    have h := oDot_value k t.nOut Ω ι PF D trivial t.g e
    unfold oDot at h
    rw [← h]
    simp [S, TExpansion.forget, List.map_map, Function.comp_def]

private theorem multiEHat_valR (A : ModelAdm Ω ι PF D) (x : Atom k n) (Γ : Graph k n)
    (hpl : ∀ c ∈ Γ.comps, c.isPlainB = true) {E : TExpansion k n}
    (hE : multiEHat x Γ = some E) (e : Fin k → ι) (ω : Ω) :
    S PF D e ω E = Γ.valR PF D e ω := by
  unfold multiEHat at hE
  split_ifs at hE
  · exact multiEOut_valR A x Γ hpl hE e ω
  · obtain ⟨E₀, hE₀, rfl⟩ := Option.map_eq_some_iff.1 hE
    obtain ⟨i₁, is₂, e₁, -, -, -, hE₀'⟩ := multiEOut_some x Γ.conj hE₀
    rw [S_conj A E₀ (hE₀' ▸ oOut_OK x Γ.conj i₁ is₂ e₁ (PB_of_plain (conj_plain hpl))),
      multiEOut_valR (conjAdm A) x Γ.conj (conj_plain hpl) hE₀ e ω, valR_eq_star A Γ hpl]
  · exact multiEIn_valR A x Γ hpl hE e ω
  · obtain ⟨E₀, hE₀, rfl⟩ := Option.map_eq_some_iff.1 hE
    obtain ⟨i₁, is₂, e₁, -, -, -, hE₀'⟩ := multiEIn_some x Γ.conj hE₀
    rw [S_conj A E₀ (hE₀' ▸ iOut_OK x Γ.conj i₁ is₂ e₁ (PB_of_plain (conj_plain hpl))),
      multiEIn_valR (conjAdm A) x Γ.conj (conj_plain hpl) hE₀ e ω, valR_eq_star A Γ hpl]

private theorem oMultiET_valR (A : ModelAdm Ω ι PF D) (x : Atom k n) (Γ : Graph k n)
    (e : Fin k → ι) (ω : Ω) : S PF D e ω (oMultiET x Γ) = Γ.valR PF D e ω := by
  unfold oMultiET
  split_ifs with hp
  · simp [S, TExpansion.forget, Expansion.valR, Tracked.self]
  · have hpl : ∀ c ∈ Γ.comps, c.isPlainB = true := by
      simpa using hp
    split
    · rename_i E hE
      rw [S_bind_oDot, multiEHat_valR A x Γ hpl hE]
    · simp [S, TExpansion.forget, Expansion.valR, Tracked.self]

private theorem oGGT_valR (A : ModelAdm Ω ι PF D) (x : Atom k n) (Γ : Graph k n)
    (e : Fin k → ι) (ω : Ω) : S PF D e ω (oGGT x Γ) = Γ.valR PF D e ω := by
  unfold oGGT
  split_ifs with hp
  · simp [S, TExpansion.forget, Expansion.valR, Tracked.self]
  · have hpl : ∀ c ∈ Γ.comps, c.isPlainB = true := by
      simpa using hp
    split
    · rename_i E hE
      rw [S_bind_oDot, ggPos_valR A x Γ hpl hE]
    · split
      · rename_i E hE
        obtain ⟨i, j, ea, eb, -, -, -, -, -, hE'⟩ := ggPos_some x Γ.conj hE
        rw [S_bind_oDot, S_conj A E (hE' ▸ ggOut_OK x Γ.conj i j ea eb
          (PB_of_plain (conj_plain hpl))), ggPos_valR (conjAdm A) x Γ.conj (conj_plain hpl) hE,
          valR_eq_star A Γ hpl]
      · simp [S, TExpansion.forget, Expansion.valR, Tracked.self]

end Assembly

/-! ## Value preservation of `O_multi-e`, `O_GG`, `O_GḠ` -/

/-- [I, Def 3.11] = [II, Def 4.4]: `O^{(x)}_multi-e` preserves the value of every graph under the
model relations ([I, Lemma 3.10] in cases (i), (ii); the identity behind [I, (3.14)] in cases
(iii), (iv); `O_dot` afterwards). -/
theorem oMultiE_value (k n : ℕ) (x : Atom k n) :
    PreservesValue (oMultiE x) modelAdm := by
  intro Ω ι _ _ PF D hA Γ e
  obtain ⟨A⟩ := hA
  funext ω
  exact oMultiET_valR A x Γ e ω

/-- [I, Def 3.15] = [II, Def 4.5]: `O^{(x)}_GG` preserves the value of every graph under the model
relations ([I, Lemma 3.14] with `b_{xα} = δ_{xα} + S⁺_{xα}`; `O_dot` afterwards). -/
theorem oGG_value (k n : ℕ) (x : Atom k n) :
    PreservesValue (oGG x) modelAdm := by
  intro Ω ι _ _ PF D hA Γ e
  obtain ⟨A⟩ := hA
  funext ω
  exact oGGT_valR A x Γ e ω

/-- [I, Def 3.18] = [II, Def 4.6]: `O^{(x)}_GḠ` preserves the value of every graph under the
model relations. -/
theorem oGGbar_value (k n : ℕ) (x : Atom k n) :
    PreservesValue (oGGbar x) modelAdm := by
  intro Ω ι _ _ PF D hA Γ e
  obtain ⟨A⟩ := hA
  funext ω
  change S PF D e ω (oGGbarT x Γ) = Γ.valR PF D e ω
  unfold oGGbarT
  dsimp only
  split_ifs
  · exact oMultiET_valR A x Γ e ω
  · simp [S, TExpansion.forget, Expansion.valR, Tracked.self]

section Instances

end Instances

end RBM8D.Graphs
