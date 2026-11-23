module

public import RBM8D.Graph.Local.StrategyPart1
import all RBM8D.Graph.Local.StrategyPart1

@[expose] public section

/-!
# The local expansion strategy

The elementary steps of [I, Strategy 3.21] and [I, Lemma 3.22] = [II, Lemma 4.9], with the `GG`
expansion in the form whose waved edge in the main term joins `x` to an internal atom.
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs
section Perms

variable {α : Type*}

private theorem eraseIdx_perm {l : List α} {i : ℕ} {a : α} (h : l[i]? = some a) :
    (l.eraseIdx i ++ [a]).Perm l := by
  induction l generalizing i with
  | nil => simp at h
  | cons b l ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      simp only [List.eraseIdx_cons_succ, List.cons_append]
      exact (ih h).cons b

private theorem eraseIdxs_two_perm {l : List α} {i j : ℕ} {a b : α} (hij : i ≠ j) (ha : l[i]? =
    some a)
    (hb : l[j]? = some b) : (eraseIdxs [i, j] l ++ [a, b]).Perm l := by
  have h1 := eraseIdxs_pick_perm [i, j] l
  have h2 := pickIdxs_perm [i, j] (by simpa using hij) l
  simp only [List.filterMap_cons, ha, hb, List.filterMap_nil] at h2
  exact ((List.Perm.refl _).append h2.symm).trans h1

end Perms

section OutDefs

variable {k n : ℕ} (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ) (e₁ : Comp (Atom k n))

/-- The tracked graph with `n + 1` internal atoms and the atom map `liftA 1`. -/
def t1 (cs : List (Comp (Atom k (n + 1)))) (d : Coeff) : Tracked k n := ⟨n + 1, ⟨cs, d⟩,
    liftA 1⟩

/-- The indices of the solid edges attached to `x`: those of charge `plus` leaving `x`, then those
of charge `minus` leaving `x`, then those of charge `plus` entering `x`, then those of charge
`minus` entering `x` ([I, Def 3.11]). -/
def oXIdx : List ℕ :=
  Γ.edgeIdx x .plus true ++ Γ.edgeIdx x .minus true ++ Γ.edgeIdx x .plus false ++
    Γ.edgeIdx x .minus false

/-- The waved edge `s_{xα}` from the image of `x` to the new atom `α` ([I, (3.13)]). -/
def oSx : Comp (Atom k (n + 1)) := mkC (.waved .s) (liftA 1 x) (newA 0)

/-- The solid edge `G_{α y₁}` taking the place of the first edge `G_{x y₁}` of charge `plus`
leaving `x` ([I, (3.13)]). -/
def oGy : Comp (Atom k (n + 1)) := mkC (.G .plus) (newA 0) (liftA 1 e₁.y)

/-- The components of a main term of [I, (3.13)] in case (i): the edges `G_{x y₁}` and `Ḡ_{x y_j}`
are exchanged for `s_{xα} G_{α y₁} Ḡ_{α y_j}`. -/
def oBaseM (j : ℕ) : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
    [oSx x, oGy e₁, mkC (.G .minus) (newA 0) (liftA 1 ((Γ.comps.getD j e₁).y))]

/-- The components of a main term of [I, (3.13)] in case (i): the edges `G_{x y₁}` and `G_{w_j x}`
are exchanged for `s_{xα} G_{α y₁} G_{w_j α}`. -/
def oBaseP (j : ℕ) : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
    [oSx x, oGy e₁, mkC (.G .plus) (liftA 1 ((Γ.comps.getD j e₁).x)) (newA 0)]

/-- The components of the term of [I, (3.13)] in case (i) in which `G_{x y₁}` is exchanged for
`s_{xα} G_{xα} G_{α y₁}`. -/
def oE1 : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (Γ.comps.eraseIdx i₁) ++ [oSx x, mkC (.G .plus) (liftA 1 x) (newA 0), oGy e₁]

/-- The components of the term of [I, (3.13)] in case (i) in which `G_{x y₁}` is exchanged for
`s_{xα} Ḡ_{αx} G_{α y₁}`. -/
def oE2 : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (Γ.comps.eraseIdx i₁) ++ [oSx x, mkC (.G .minus) (newA 0) (liftA 1 x), oGy e₁]

/-- The components of the term `m ∑_α s_{xα} (G_{αα} - m) 𝒢` of [I, (3.13)] in case (i). -/
def oL3 : List (Comp (Atom k (n + 1))) :=
  liftCs 1 Γ.comps ++ [oSx x, mkC (.light .plus) (newA 0) (newA 0)]

/-- The components of the derivative terms of [I, (3.13)] in case (i). -/
def oDs : List (List (Comp (Atom k (n + 1)))) :=
  (dTerms (newA 0) (liftA 1 x) (liftCs 1 (eraseIdxs (oXIdx x Γ) Γ.comps))).map fun d =>
    liftCs 1 (pickIdxs ((oXIdx x Γ).filter (· != i₁)) Γ.comps) ++ d ++ [oSx x, oGy e₁]

/-- The terms of `Ô^{(x)}_multi-e` in case (i) of [I, Def 3.11], for the first edge `G_{x y₁}` of
charge `plus` leaving `x` (at the index `i₁`, the further such edges being at the indices
`is₂`). -/
def oOut : TExpansion k n :=
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

end OutDefs

section OutTerms

variable {k n : ℕ}

/-- The data of case (i) of [I, Def 3.11]: `Γ` is plain and normal regular with bound `C`, label-
free, `x` is internal, and the edges of charge `plus` leaving `x` are at the indices `i₁ ::
is₂`, the first being `e₁`. -/
structure OutCtxS (C : ℕ) (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ)
    (e₁ : Comp (Atom k n)) : Prop where
  normal : Γ.Normal C
  plain : Γ.Plain
  right : x.isRight = true
  unl : ∀ c ∈ Γ.comps, c.label = none
  hOP : Γ.edgeIdx x .plus true = i₁ :: is₂
  hL : Γ.comps[i₁]? = some e₁

private theorem OutCtxS.e₁spec {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : OutCtxS C x Γ i₁ is₂ e₁) :
    e₁.kind = .G .plus ∧ e₁.x = x ∧ e₁.y ≠ x := by
  have h : i₁ ∈ Γ.edgeIdx x .plus true := by rw [Ctx.hOP]; exact List.mem_cons_self ..
  obtain ⟨c, hc, hk, ho⟩ := mem_edgeIdx.1 h
  rw [Ctx.hL] at hc
  obtain rfl := Option.some.inj hc
  exact ⟨hk, ho⟩

private theorem OutCtxS.e₁mem {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : OutCtxS C x Γ i₁ is₂ e₁) : e₁ ∈ Γ.comps :=
  List.mem_of_getElem? Ctx.hL

end OutTerms

section XIdx

private theorem perm_aux {α : Type*} (xe fL : List α) (e : α) :
    (xe ++ fL ++ [e]).Perm (fL ++ (e :: xe)) := by
  have h : (fL ++ (e :: xe)).Perm (xe ++ fL ++ [e]) := by
    rw [← Multiset.coe_eq_coe]
    have : (e :: xe) = [e] ++ xe := rfl
    rw [this]
    simp only [← Multiset.coe_add]
    abel
  exact h.symm

variable {k n : ℕ}

private theorem mem_eraseIdxs_iff {α : Type*} {is : List ℕ} {l : List α} {c : α} :
    c ∈ eraseIdxs is l ↔ ∃ i, l[i]? = some c ∧ i ∉ is := by
  rw [eraseIdxs_eq, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [List.mem_filter, List.mem_zipIdx_iff_getElem?] at hp
    refine ⟨p.2, hp.1, ?_⟩
    simpa using hp.2
  · rintro ⟨i, hi, hn⟩
    refine ⟨(c, i), ?_, rfl⟩
    rw [List.mem_filter, List.mem_zipIdx_iff_getElem?]
    exact ⟨hi, by simpa using hn⟩

theorem mem_oXIdx {Γ : Graph k n} {x : Atom k n} {j : ℕ} :
    j ∈ oXIdx x Γ ↔ ∃ c, Γ.comps[j]? = some c ∧ ∃ ch, c.kind = .G ch ∧
      ((c.x = x ∧ c.y ≠ x) ∨ (c.y = x ∧ c.x ≠ x)) := by
  unfold oXIdx
  simp only [List.mem_append, mem_edgeIdx]
  constructor
  · rintro (((⟨c, h1, h2, h3⟩ | ⟨c, h1, h2, h3⟩) | ⟨c, h1, h2, h3⟩) | ⟨c, h1, h2, h3⟩)
    · exact ⟨c, h1, _, h2, Or.inl h3⟩
    · exact ⟨c, h1, _, h2, Or.inl h3⟩
    · exact ⟨c, h1, _, h2, Or.inr h3⟩
    · exact ⟨c, h1, _, h2, Or.inr h3⟩
  · rintro ⟨c, h1, ch, h2, h3 | h3⟩
    · cases ch
      · exact Or.inl (Or.inl (Or.inl ⟨c, h1, h2, h3⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨c, h1, h2, h3⟩))
    · cases ch
      · exact Or.inl (Or.inr ⟨c, h1, h2, h3⟩)
      · exact Or.inr ⟨c, h1, h2, h3⟩

private theorem oXIdx_nodup (x : Atom k n) (Γ : Graph k n) : (oXIdx x Γ).Nodup := by
  unfold oXIdx
  have n1 := edgeIdx_nodup Γ x .plus true
  have n2 := edgeIdx_nodup Γ x .minus true
  have n3 := edgeIdx_nodup Γ x .plus false
  have n4 := edgeIdx_nodup Γ x .minus false
  simp only [List.nodup_append]
  refine ⟨⟨⟨n1, n2, ?_⟩, n3, ?_⟩, n4, ?_⟩
  · intro a ha b hb hab
    subst hab
    exact edgeIdx_disjoint (Or.inl (by simp)) ha hb
  · intro a ha b hb hab
    subst hab
    rcases List.mem_append.1 ha with ha | ha
    · exact edgeIdx_disjoint (Or.inr (by simp)) ha hb
    · exact edgeIdx_disjoint (Or.inr (by simp)) ha hb
  · intro a ha b hb hab
    subst hab
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_append.1 ha with ha | ha
      · exact edgeIdx_disjoint (Or.inr (by simp)) ha hb
      · exact edgeIdx_disjoint (Or.inr (by simp)) ha hb
    · exact edgeIdx_disjoint (Or.inl (by simp)) ha hb

private theorem oXIdx_mem_i₁ {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : OutCtxS C x Γ i₁ is₂ e₁) : i₁ ∈ oXIdx x Γ := by
  have : i₁ ∈ Γ.edgeIdx x .plus true := by rw [Ctx.hOP]; exact List.mem_cons_self ..
  unfold oXIdx
  simp [this]

private theorem xe_fL_perm {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : OutCtxS C x Γ i₁ is₂ e₁) :
    (pickIdxs ((oXIdx x Γ).filter (· != i₁)) Γ.comps ++ eraseIdxs (oXIdx x Γ) Γ.comps ++
      [e₁]).Perm Γ.comps := by
  have hnd := oXIdx_nodup x Γ
  have hmem := oXIdx_mem_i₁ Ctx
  have hP1 := pickIdxs_perm ((oXIdx x Γ).filter (· != i₁))
    (hnd.sublist (List.filter_sublist)) Γ.comps
  have hP2 := pickIdxs_perm (oXIdx x Γ) hnd Γ.comps
  have hxI : (oXIdx x Γ).Perm (i₁ :: (oXIdx x Γ).filter (· != i₁)) := by
    have := List.perm_cons_erase hmem
    rwa [hnd.erase_eq_filter] at this
  have hP3 := hxI.filterMap (fun i => Γ.comps[i]?)
  simp only [List.filterMap_cons, Ctx.hL] at hP3
  have hall : (pickIdxs (oXIdx x Γ) Γ.comps).Perm
      (e₁ :: pickIdxs ((oXIdx x Γ).filter (· != i₁)) Γ.comps) :=
    hP2.trans (hP3.trans (hP1.symm.cons e₁))
  have h1 := eraseIdxs_pick_perm (oXIdx x Γ) Γ.comps
  refine List.Perm.trans ?_ ((hall.symm.append_left _).trans h1)
  exact perm_aux _ _ _

end XIdx

section ZeroLift

private theorem comp_map_id' {V : Type*} (c : Comp V) : c.map id = c := by
  cases c; simp [Comp.map]

variable {k n : ℕ}

private theorem liftA_zero (u : Atom k n) : (liftA 0 u : Atom k (n + 0)) = u := by
  rcases u with a | a <;> simp [liftA]

private theorem liftA_zero_eq : (liftA 0 : Atom k n → Atom k (n + 0)) = id := funext liftA_zero

private theorem liftCs_zero (cs : List (Comp (Atom k n))) :
    (liftCs 0 cs : List (Comp (Atom k (n + 0)))) = cs := by
  unfold liftCs
  simp only [liftA_zero_eq]
  rw [show Comp.map (id : Atom k n → Atom k n) = id from funext comp_map_id', List.map_id]

end ZeroLift

section GGDefs2

variable {k n : ℕ} (x : Atom k n) (Γ : Graph k n) (i j : ℕ) (e e' : Comp (Atom k n))

/-- The tracked graph with `n + 2` internal atoms and the atom map `liftA 2`. -/
def t2 (cs : List (Comp (Atom k (n + 2)))) (d : Coeff) : Tracked k n := ⟨n + 2, ⟨cs, d⟩,
    liftA 2⟩

/-- The components of `Γ` other than the two solid edges at the indices `i` and `j`. -/
def ggF : List (Comp (Atom k n)) := eraseIdxs [i, j] Γ.comps

/-- The components `f G_{y'y}` (with the weight `G_{yy}` when `y = y'`) of the main term of
`Ô^{(x)}_GG` ([I, (3.17)]). -/
def ggMain : List (Comp (Atom k n)) := ggF Γ i j ++ [solidC .plus e'.x e.y]

/-- The derivative terms of `f` at `α` in `Ô^{(x)}_GG` ([I, (3.17)]), with one new atom. -/
def ggD1 : List (List (Comp (Atom k (n + 1)))) :=
  (dTerms (newA 0) (liftA 1 x) (liftCs 1 (ggF Γ i j))).map fun d =>
    d ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)]

/-- The derivative terms of `f` at `β` in `Ô^{(x)}_GG` ([I, (3.17)]), with two new atoms. -/
def ggD2 : List (List (Comp (Atom k (n + 2)))) :=
  (dTerms (newA 1) (newA 0) (liftCs 2 (ggF Γ i j))).map fun d =>
    d ++ [mkC (.G .plus) (newA 1) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 0)]

/-- The terms of `Ô^{(x)}_GG` ([I, (3.17)]) for the edges `e = G_{xy}` at the index `i` and `e' =
G_{y'x}` at the index `j`. -/
def ggOut : TExpansion k n :=
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

end GGDefs2

section GGCtx

variable {k n : ℕ}

/-- The data of the `GG` expansion: `Γ` is plain and normal regular with bound `C`, label-free,
`x` is internal, and the solid edges attached to `x` are the edge `e` of charge `plus` leaving
`x` (index `i`) and the edge `e'` of charge `plus` entering `x` (index `j`). -/
structure GGCtxS (C : ℕ) (x : Atom k n) (Γ : Graph k n) (i j : ℕ) (e e' : Comp (Atom k n)) :
    Prop where
  normal : Γ.Normal C
  plain : Γ.Plain
  right : x.isRight = true
  unl : ∀ c ∈ Γ.comps, c.label = none
  hPO : Γ.edgeIdx x .plus true = [i]
  hPI : Γ.edgeIdx x .plus false = [j]
  hMO : Γ.edgeIdx x .minus true = []
  hMI : Γ.edgeIdx x .minus false = []
  hi : Γ.comps[i]? = some e
  hj : Γ.comps[j]? = some e'

theorem GGCtxS.espec {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k
    n)}
    (Ctx : GGCtxS C x Γ i j e e') : e.kind = .G .plus ∧ e.x = x ∧ e.y ≠ x := by
  have h : i ∈ Γ.edgeIdx x .plus true := by rw [Ctx.hPO]; exact List.mem_singleton_self _
  obtain ⟨c, hc, hk, ho⟩ := mem_edgeIdx.1 h
  rw [Ctx.hi] at hc
  obtain rfl := Option.some.inj hc
  exact ⟨hk, ho⟩

theorem GGCtxS.e'spec {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k
    n)}
    (Ctx : GGCtxS C x Γ i j e e') : e'.kind = .G .plus ∧ e'.y = x ∧ e'.x ≠ x := by
  have h : j ∈ Γ.edgeIdx x .plus false := by rw [Ctx.hPI]; exact List.mem_singleton_self _
  obtain ⟨c, hc, hk, ho⟩ := mem_edgeIdx.1 h
  rw [Ctx.hj] at hc
  obtain rfl := Option.some.inj hc
  exact ⟨hk, ho⟩

private theorem GGCtxS.hij {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k n)}
    (Ctx : GGCtxS C x Γ i j e e') : i ≠ j := by
  intro hij
  have hj := Ctx.hj
  rw [← hij, Ctx.hi] at hj
  obtain rfl := Option.some.inj hj
  exact Ctx.e'spec.2.2 Ctx.espec.2.1

private theorem GGCtxS.perm {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k n)}
    (Ctx : GGCtxS C x Γ i j e e') : (ggF Γ i j ++ [e, e']).Perm Γ.comps :=
  eraseIdxs_two_perm Ctx.hij Ctx.hi Ctx.hj

set_option linter.flexible false in
private theorem GGCtxS.f_untouched {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ}
    {e e' : Comp (Atom k n)} (Ctx : GGCtxS C x Γ i j e e') {c : Comp (Atom k n)}
    (hc : c ∈ ggF Γ i j) {ch : Charge} (hk : c.kind = .G ch) : c.x ≠ x ∧ c.y ≠ x := by
  obtain ⟨m, hm, hn⟩ := mem_eraseIdxs_iff.1 hc
  have hcm : c ∈ Γ.comps := mem_eraseIdxs_of_mem hc
  have hsl := Ctx.normal.2.1 c hcm (by simp [hk, Kind.isSolid])
  have hmi : m ≠ i := fun h => hn (by simp [h])
  have hmj : m ≠ j := fun h => hn (by simp [h])
  constructor
  · intro hcx
    have hy : c.y ≠ x := by rw [← hcx]; exact fun h => hsl h.symm
    have : m ∈ Γ.edgeIdx x ch true := mem_edgeIdx.2 ⟨c, hm, hk, hcx, hy⟩
    cases ch
    · rw [Ctx.hPO] at this; simp at this; exact hmi this
    · rw [Ctx.hMO] at this; simp at this
  · intro hcy
    have hxx : c.x ≠ x := by rw [← hcy]; exact hsl
    have : m ∈ Γ.edgeIdx x ch false := mem_edgeIdx.2 ⟨c, hm, hk, hcy, hxx⟩
    cases ch
    · rw [Ctx.hPI] at this; simp at this; exact hmj this
    · rw [Ctx.hMI] at this; simp at this

private theorem GGCtxS.e'mem {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k
    n)}
    (Ctx : GGCtxS C x Γ i j e e') : e' ∈ Γ.comps := List.mem_of_getElem? Ctx.hj

private theorem GGCtxS.emem {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k n)}
    (Ctx : GGCtxS C x Γ i j e e') : e ∈ Γ.comps := List.mem_of_getElem? Ctx.hi

end GGCtx

/-! ## Building the schema of a term -/

section SchMk

variable {k n : ℕ}

private theorem sch_mk {Γ : Graph k n} {j : ℕ} {K R : List (Comp (Atom k n))}
    (hR : ∀ c ∈ R, c.kind.isRandom = true) (hK : Γ.comps.Perm (K ++ R))
    (lab : Option (Atom k (n + j))) (N₁ N₂ : List (Comp (Atom k (n + j))))
    (hN₂ : ∀ c ∈ N₂, c.kind.isRandom = false) {cs : List (Comp (Atom k (n + j)))}
    (hcs : cs.Perm (labW lab (liftCs j K ++ N₁) ++ N₂)) (d : Coeff) :
    Sch Γ j R (N₁ ++ N₂) lab ⟨cs, d⟩ := by
  refine ⟨hR, K, hK, hcs.trans (List.Perm.of_eq ?_)⟩
  have h2 : N₂.map (labF lab) = N₂ := by
    conv_rhs => rw [← List.map_id N₂]
    exact List.map_congr_left (fun c hc => labF_nonrandom lab (hN₂ c hc))
  rw [labW_eq_map]
  simp only [List.map_append, List.append_assoc, h2]

private theorem tracked_id_eq {g : Graph k n} : (⟨n, g, id⟩ : Tracked k n) = ⟨n + 0, g, liftA 0⟩ := by
  congr 1
  exact (funext liftA_zero).symm

/-- A term of the derivative: the component `c` of `F` is replaced by its two factors. -/
private theorem dTerms_lift_split {j : ℕ} {p q : Atom k (n + j)} {F : List (Comp (Atom k n))}
    {d : List (Comp (Atom k (n + j)))} (hd : d ∈ dTerms p q (liftCs j F)) :
    ∃ c K ps, F.Perm (K ++ [c]) ∧ c ∈ F ∧ (c.map (liftA j)).dPieces p q = some ps ∧
      d = liftCs j K ++ ps := by
  obtain ⟨m, hm, ps, hps, rfl⟩ := mem_dTerms.1 hd
  have hm' : m < F.length := by simpa [liftCs] using hm
  refine ⟨F[m], F.eraseIdx m, ps, (eraseIdx_perm (by simp [hm'])).symm, List.getElem_mem hm',
    ?_, ?_⟩
  · simpa [liftCs] using hps
  · unfold liftCs
    rw [eraseIdx_map]

@[simp] private theorem newA_ne_liftA' {j : ℕ} (i : Fin j) (u : Atom k n) : (newA i : Atom k (n + j)) ≠ liftA j u :=
  fun h => liftA_ne_newA j u i h.symm

@[simp] private theorem liftA_ne_newA' {j : ℕ} (i : Fin j) (u : Atom k n) : liftA j u ≠ (newA i : Atom k (n + j)) :=
  liftA_ne_newA j u i

@[simp] private theorem liftA_inj' {j : ℕ} {u v : Atom k n} : liftA j u = liftA j v ↔ u = v :=
  (liftA_injective j).eq_iff

@[simp] private theorem newA01 : (newA 0 : Atom k (n + 2)) ≠ newA 1 := by
  simp [newA, Fin.ext_iff]

@[simp] private theorem newA10 : (newA 1 : Atom k (n + 2)) ≠ newA 0 := by
  simp [newA, Fin.ext_iff]

@[simp] private theorem isRight_newA {j : ℕ} (i : Fin j) : (newA i : Atom k (n + j)).isRight = true := rfl

@[simp] private theorem isLeft_newA {j : ℕ} (i : Fin j) : (newA i : Atom k (n + j)).isLeft = false := rfl

@[simp] private theorem isRight_liftA {j : ℕ} (u : Atom k n) : (liftA j u).isRight = u.isRight :=
  liftA_isRight j u

@[simp] private theorem isLeft_liftA {j : ℕ} (u : Atom k n) : (liftA j u).isLeft = u.isLeft :=
  liftA_isLeft j u

@[simp] private theorem isNewA_liftA' {j : ℕ} (u : Atom k n) : isNewA n (liftA j u) = false :=
  isNewA_liftA u

@[simp] private theorem isNewA_newA' {j : ℕ} (i : Fin j) : isNewA n (newA i : Atom k (n + j)) = true :=
  isNewA_newA i

private theorem solidC_of_ne {V : Type*} [DecidableEq V] {ch : Charge} {u v : V} (h : u ≠ v) :
    solidC ch u v = mkC (.G ch) u v := by
  unfold solidC; rw [if_neg h]

private theorem solidC_self {V : Type*} [DecidableEq V] (ch : Charge) (u : V) :
    solidC ch u u = mkC (.weight ch) u u := by
  unfold solidC; rw [if_pos rfl]

private theorem newOK_label {V : Type*} [DecidableEq V] :
    (∀ (κ : Kind) (u v : V), (mkC κ u v).label = none) ∧
    ∀ (ch : Charge) (u v : V), (solidC ch u v).label = none := by
  refine ⟨fun _ _ _ => rfl, fun ch u v => ?_⟩
  unfold solidC; split_ifs <;> rfl

end SchMk

/-! ## Constructing `TermOK` -/

section TermMk

variable {k n : ℕ}

private theorem termOKS_mk (sw : Bool) {Γ : Graph k n} {x : Atom k n} {j : ℕ}
    {K R : List (Comp (Atom k n))}
    (lab : Option (Atom k (n + j))) (N₁ N₂ : List (Comp (Atom k (n + j))))
    {cs : List (Comp (Atom k (n + j)))} (d : Coeff) (s : ℕ)
    (hK : Γ.comps.Perm (K ++ R)) (hR : ∀ c ∈ R, c.kind.isRandom = true)
    (hcs : cs.Perm (labW lab (liftCs j K ++ N₁) ++ N₂))
    (hN₂ : ∀ c ∈ N₂, c.kind.isRandom = false)
    (hNo : ∀ c ∈ N₁ ++ N₂, NewOK c ∧ c.label = none)
    (hNK : ∀ c ∈ N₁ ++ N₂, c.kind.isRandom = true → (kAt sw c).isRight = true)
    (hs : ordL (N₁ ++ N₂) = ordL R + 2 * j + s)
    (two : ∀ i : Fin j, ((N₁ ++ N₂).filter fun c => c.kind.isSolid && atB (newA i) c).length ≤ 2)
    (excl : Atom k (n + j) → Atom k (n + j) → Bool)
    (hexcl : ∀ c ∈ N₁ ++ N₂, excl c.x c.y = true →
      ∃ a b, c.x = liftA j a ∧ c.y = liftA j b ∧ Γ.hasXdot a b = true)
    (old : ((N₁ ++ N₂).filter fun c => c.kind.isSolid && !isNewA n c.x && !isNewA n c.y &&
      !excl c.x c.y).length ≤ s)
    (four : ((N₁ ++ N₂).filter fun c => c.kind.isSolid).length ≤ 4)
    (zero : s = 0 → ((N₁ ++ N₂).filter fun c => c.kind.isSolid).length ≤ 2)
    (hext : ((N₁ ++ N₂).filter fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length ≤
      (R.filter fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length)
    (hphi : lab = none → s = 0 →
      (⟨cs, d⟩ : Graph k (n + j)).phi + (if j = 0 then 1 else 3) ≤ Γ.phi)
    (hlab : lab ≠ none → ∃ c ∈ cs, c.kind.isRandom = true)
    (att : ∀ i : Fin j, (⟨cs, d⟩ : Graph k (n + j)).SameMol (liftA j x) (newA i)) :
    TermOKS sw Γ x ⟨n + j, ⟨cs, d⟩, liftA j⟩ := by
  have hS := sch_mk hR hK lab N₁ N₂ hN₂ hcs d
  refine ⟨j, R, N₁ ++ N₂, lab, ⟨cs, d⟩, s, rfl, hS, hNo, hNK, hs, two,
    le_trans (length_filter_mono _ _ _ fun c hc h => ?_) old, four, zero, hext, hphi, hlab, att⟩
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
  refine ⟨⟨⟨h.1.1.1, h.1.2⟩, h.2⟩, ?_⟩
  by_contra hex
  rw [Bool.not_eq_false] at hex
  obtain ⟨a, b, ha, hb, hab⟩ := hexcl c hc hex
  have := hS.hasXdot_lift (fun c hc => (hNo c hc).1.ne_xdot') a b
  rw [← ha, ← hb, hab, h.1.1.2] at this
  cases this

private theorem termOK_mk {Γ : Graph k n} {x : Atom k n} {j : ℕ} {K R : List (Comp (Atom k n))}
    (lab : Option (Atom k (n + j))) (N₁ N₂ : List (Comp (Atom k (n + j))))
    {cs : List (Comp (Atom k (n + j)))} (d : Coeff) (s : ℕ)
    (hK : Γ.comps.Perm (K ++ R)) (hR : ∀ c ∈ R, c.kind.isRandom = true)
    (hcs : cs.Perm (labW lab (liftCs j K ++ N₁) ++ N₂))
    (hN₂ : ∀ c ∈ N₂, c.kind.isRandom = false)
    (hNo : ∀ c ∈ N₁ ++ N₂, NewOK c ∧ c.label = none)
    (hNK : ∀ c ∈ N₁ ++ N₂, c.kind.isRandom = true → c.x.isRight = true)
    (hs : ordL (N₁ ++ N₂) = ordL R + 2 * j + s)
    (two : ∀ i : Fin j, ((N₁ ++ N₂).filter fun c => c.kind.isSolid && atB (newA i) c).length ≤ 2)
    (excl : Atom k (n + j) → Atom k (n + j) → Bool)
    (hexcl : ∀ c ∈ N₁ ++ N₂, excl c.x c.y = true →
      ∃ a b, c.x = liftA j a ∧ c.y = liftA j b ∧ Γ.hasXdot a b = true)
    (old : ((N₁ ++ N₂).filter fun c => c.kind.isSolid && !isNewA n c.x && !isNewA n c.y &&
      !excl c.x c.y).length ≤ s)
    (four : ((N₁ ++ N₂).filter fun c => c.kind.isSolid).length ≤ 4)
    (zero : s = 0 → ((N₁ ++ N₂).filter fun c => c.kind.isSolid).length ≤ 2)
    (hext : ((N₁ ++ N₂).filter fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length ≤
      (R.filter fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length)
    (hphi : lab = none → s = 0 → (⟨cs, d⟩ : Graph k (n + j)).phi + 3 ≤ Γ.phi)
    (hlab : lab ≠ none → ∃ c ∈ cs, c.kind.isRandom = true)
    (att : ∀ i : Fin j, (⟨cs, d⟩ : Graph k (n + j)).SameMol (liftA j x) (newA i)) :
    TermOK Γ x ⟨n + j, ⟨cs, d⟩, liftA j⟩ :=
  termOKS_mk false lab N₁ N₂ d s hK hR hcs hN₂ hNo hNK hs two excl hexcl old four zero hext
    (fun hl hs0 => le_trans (by split_ifs <;> omega) (hphi hl hs0)) hlab att

/-- A new atom joined by a waved edge of the new components to an atom. -/
private theorem sameMol_of_waved {m : ℕ} {g : Graph k m} {w : Wave} {a b : Atom k m}
    (h : mkC (.waved w) a b ∈ g.comps) (ha : a.isRight = true) (hb : b.isRight = true) :
    g.SameMol a b :=
  Or.inr ⟨ha, hb, Graph.molReach_of_comp h (by simp [mkC, Kind.joinsMol])⟩

end TermMk

/-! ## The terms of the `GG` expansion -/

section GGFam

variable {k n : ℕ}

/-- The hypotheses of the `GG` expansion at `x` used for its terms. -/
private structure GGHyp (sw : Bool) (C : ℕ) (x : Atom k n) (Γ : Graph k n) (i j : ℕ)
    (e e' : Comp (Atom k n)) : Prop where
  ctx : GGCtxS C x Γ i j e e'
  K0 : ∀ c ∈ Γ.comps, c.kind.isRandom = true → (kAt sw c).isRight = true
  wt0 : Γ.wt x = 0
  deg2 : Γ.deg x = 2

variable {sw : Bool} {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k n)}

private theorem kAt_nonsolid {V : Type*} (sw : Bool) (c : Comp V) (h : c.kind.isSolid = false) :
    kAt sw c = c.x := by
  cases sw <;> simp [kAt, h]

private theorem kAt_G_of {m : ℕ} {sw : Bool} {ch : Charge} {u v : Atom k m}
    (h1 : sw = false → u.isRight = true) (h2 : sw = true → v.isRight = true) :
    (kAt sw (mkC (.G ch) u v)).isRight = true := by
  cases sw
  · exact h1 rfl
  · exact h2 rfl

private theorem kAt_ns_of {m : ℕ} {sw : Bool} {c : Comp (Atom k m)} (h : c.kind.isSolid = false)
    (h1 : c.x.isRight = true) : (kAt sw c).isRight = true := by
  rw [kAt_nonsolid sw c h]; exact h1


private theorem hasXdot_of_solid {C : ℕ} {Γ : Graph k n} (hN : Γ.Normal C) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hs : c.kind.isSolid = true) : Γ.hasXdot c.x c.y = true := by
  obtain ⟨-, hl, hx⟩ := hN
  obtain ⟨d, hd, hdk, hdxy⟩ := (hx c.x c.y (hl c hc hs)).2 ⟨c, hc, hs, Or.inl ⟨rfl, rfl⟩⟩
  simp only [Graph.hasXdot, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
  exact ⟨d, hd, hdk, hdxy⟩

private theorem hasXdot_comm (Γ : Graph k n) (u v : Atom k n) : Γ.hasXdot u v = Γ.hasXdot v u := by
  simp only [Graph.hasXdot]
  congr 1
  funext c
  cases (c.x == u) <;> cases (c.y == v) <;> cases (c.x == v) <;> cases (c.y == u) <;> rfl

/-- The basic facts of the `GG` expansion. -/
private theorem GGHyp.facts (H : GGHyp sw C x Γ i j e e') :
    e.kind = .G .plus ∧ e.x = x ∧ e.y ≠ x ∧ e'.kind = .G .plus ∧ e'.y = x ∧ e'.x ≠ x ∧
    (sw = false → e'.x.isRight = true) ∧ x.isRight = true ∧ Γ.hasXdot x e.y = true ∧
    Γ.hasXdot e'.x x = true ∧
    Γ.comps.Perm (ggF Γ i j ++ [e, e']) ∧ e ∈ Γ.comps ∧ e' ∈ Γ.comps := by
  obtain ⟨h1, h2, h3⟩ := H.ctx.espec
  obtain ⟨h4, h5, h6⟩ := H.ctx.e'spec
  have he := H.ctx.emem
  have he' := H.ctx.e'mem
  refine ⟨h1, h2, h3, h4, h5, h6, fun hsw => ?_, H.ctx.right, ?_, ?_,
    H.ctx.perm.symm, he, he'⟩
  · have := H.K0 e' he' (by simp [h4, Kind.isRandom])
    subst hsw
    exact this
  · have := hasXdot_of_solid H.ctx.normal he (by simp [h1, Kind.isSolid])
    rwa [h2] at this
  · have := hasXdot_of_solid H.ctx.normal he' (by simp [h4, Kind.isSolid])
    rwa [h5] at this

/-- With `sw = true`, the second atom of the edge leaving `x` is internal. -/
private theorem GGHyp.eyR (H : GGHyp sw C x Γ i j e e') : sw = true → e.y.isRight = true := by
  intro hsw
  have := H.K0 e H.ctx.emem (by simp [H.ctx.espec.1, Kind.isRandom])
  subst hsw
  simpa [kAt, H.ctx.espec.1, Kind.isSolid] using this

/-- The random components of `f` are not attached to `x`, and sit on internal atoms. -/
private theorem GGHyp.f_rand (H : GGHyp sw C x Γ i j e e') {c : Comp (Atom k n)} (hc : c ∈ ggF Γ i j)
    (hr : c.kind.isRandom = true) : c.x ≠ x ∧ c.endB ≠ x ∧
      ((sw = false → c.x.isRight = true) ∧ (sw = true → c.endB.isRight = true)) ∧
      ((∃ ch, c.kind = .G ch) ∨ (∃ ch, c.kind = .weight ch) ∨ (∃ ch, c.kind = .light ch)) := by
  have hcm : c ∈ Γ.comps := mem_eraseIdxs_of_mem hc
  obtain ⟨-, p2, p3, -, -⟩ := H.ctx.plain c hcm
  have hk : (∃ ch, c.kind = .G ch) ∨ (∃ ch, c.kind = .weight ch) ∨ (∃ ch, c.kind = .light ch) := by
    revert hr p2 p3
    cases c.kind <;> simp [Kind.isRandom]
  have hxr := H.K0 c hcm hr
  have hK : (sw = false → c.x.isRight = true) ∧ (sw = true → c.endB.isRight = true) := by
    refine ⟨fun hsw => ?_, fun hsw => ?_⟩ <;> subst hsw
    · exact hxr
    · rcases hk with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ <;>
        simpa [kAt, Comp.endB, h, Kind.isSolid, Kind.isWeight] using hxr
  rcases hk with ⟨ch, hch⟩ | hw
  · obtain ⟨h1, h2⟩ := H.ctx.f_untouched hc hch
    refine ⟨h1, ?_, hK, Or.inl ⟨ch, hch⟩⟩
    simp [Comp.endB, hch, Kind.isWeight, h2]
  · have hx : c.x ≠ x := by
      intro hcx
      have hw0 := H.wt0
      rw [Graph.wt, List.length_eq_zero_iff, List.filter_eq_nil_iff] at hw0
      have := hw0 c hcm
      rcases hw with ⟨ch, h⟩ | ⟨ch, h⟩ <;> simp [h, hcx] at this
    refine ⟨hx, ?_, hK, Or.inr hw⟩
    rcases hw with ⟨ch, h⟩ | ⟨ch, h⟩ <;> simp [Comp.endB, h, Kind.isWeight, hx]

end GGFam

section DPiecesLift

variable {k n : ℕ}

private theorem endB_map' {m : ℕ} (f : Atom k n → Atom k m) (c : Comp (Atom k n)) :
    (c.map f).endB = f c.endB := by
  unfold Comp.endB
  simp only [Comp.map]
  split_ifs <;> simp_all

/-- The factors of the derivative of a moved random component. -/
private theorem dPieces_lift {j : ℕ} {c₀ : Comp (Atom k n)} {p q : Atom k (n + j)}
    {ps : List (Comp (Atom k (n + j)))} (h : (c₀.map (liftA j)).dPieces p q = some ps) :
    ((c₀.kind = .G .plus ∨ c₀.kind = .weight .plus ∨ c₀.kind = .light .plus) ∧
      ps = [solidC .plus (liftA j c₀.x) p, solidC .plus q (liftA j c₀.endB)]) ∨
    ((c₀.kind = .G .minus ∨ c₀.kind = .weight .minus ∨ c₀.kind = .light .minus) ∧
      ps = [solidC .minus (liftA j c₀.x) q, solidC .minus p (liftA j c₀.endB)]) := by
  have hk := dPieces_random h
  rcases dPieces_eq_plus h hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    rw [endB_map'] at h2
    exact ⟨h1, h2⟩
  · right
    rw [endB_map'] at h2
    exact ⟨h1, h2⟩

private theorem kind_ord_of_pm {κ : Kind} {ch : Charge}
    (h : κ = .G ch ∨ κ = .weight ch ∨ κ = .light ch) :
    (κ.ord = 1 ∨ κ.ord = 0) ∧ (κ.ord = 0 ↔ κ = .weight ch) ∧ κ.isRandom = true := by
  rcases h with rfl | rfl | rfl <;> simp [Kind.ord, Kind.isRandom]

end DPiecesLift

section GGFam2

variable {k n : ℕ} {sw : Bool} {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k n)}

/-- `m ∑_α s_{xα} (G_{αα} - m) 𝒢`. -/
private theorem GGHyp.term2 (H : GGHyp sw C x Γ i j e e') :
    TermOKS sw Γ x (t1 (liftCs 1 Γ.comps ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.light .plus) (newA 0) (newA 0)]) (cm * Γ.coeff)) := by
  have hx := H.ctx.right
  refine termOKS_mk sw (K := Γ.comps) (R := []) none [mkC (.waved .s) (liftA 1 x) (newA 0),
    mkC (.light .plus) (newA 0) (newA 0)] [] _ 1 (by simp) (by simp) (by simp [labW]) (by simp)
    ?_ ?_ ?_ ?_ (fun _ _ => false) (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨NewOK_waved _ _ _, rfl⟩
    · exact ⟨NewOK_light _ _, rfl⟩
  · intro c hc hr
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
      (first
        | (apply kAt_G_of <;> intro _ <;> (try simp only [isRight_liftA, isRight_newA]) <;>
            solve_by_elim)
        | (apply kAt_ns_of (by simp [mkC, Kind.isSolid]) <;>
            (try simp only [mkC, isRight_liftA, isRight_newA]) <;> solve_by_elim)
        | (simp [mkC, Kind.isRandom] at *; done))
  · simp [ordL, mkC, Kind.ord]
  · intro i; simp [mkC, Kind.isSolid]
  · simp [mkC, Kind.isSolid]
  · simp [mkC, Kind.isSolid]
  · intro h; simp at h
  · simp [mkC, Kind.isSolid]
  · intro _ h; simp at h
  · intro h; simp at h
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact sameMol_of_waved (w := .s) (List.mem_append_right _ (List.mem_cons_self ..))
      (by simpa using hx) rfl

/-- The derivative terms of `f` at `α`, without or with the label `Q_x`. -/
private theorem GGHyp.termD1 (H : GGHyp sw C x Γ i j e e') {d : List (Comp (Atom k (n + 1)))}
    (hd : d ∈ ggD1 x Γ i j e e') (lab : Option (Atom k (n + 1))) (co : Coeff) :
    TermOKS sw Γ x (t1 (labW lab d ++ [mkC (.waved .s) (liftA 1 x) (newA 0)]) co) := by
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hy'R, hxR, -, hy'x, hperm, -, -⟩ := H.facts
  have heyR := H.eyR
  unfold ggD1 at hd
  obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
  obtain ⟨c₀, K, ps, hF, hc₀, hps, rfl⟩ := dTerms_lift_split hd₀
  have hpm := dPieces_lift hps
  have hr₀ : c₀.kind.isRandom = true := by
    rcases hpm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact (kind_ord_of_pm h).2.2
  obtain ⟨cx, cb, cxR, -⟩ := H.f_rand hc₀ hr₀
  have cxR1 := cxR.1
  have cxR2 := cxR.2
  have hxL : x.isLeft = false := by cases x <;> simp_all
  have hK : Γ.comps.Perm (K ++ [e, e', c₀]) := by
    refine hperm.trans ?_
    refine (hF.append_right _).trans ?_
    rw [List.append_assoc]
    exact List.Perm.append_left K (List.perm_append_comm (l₁ := [c₀]) (l₂ := [e, e']))
  have hord : c₀.kind.ord = 1 ∨ c₀.kind.ord = 0 := by
    rcases hpm with ⟨h, -⟩ | ⟨h, -⟩
    · rcases h with h | h | h <;> exact (kind_ord_of_pm (ch := .plus) (by simp [h])).1
    · rcases h with h | h | h <;> exact (kind_ord_of_pm (ch := .minus) (by simp [h])).1
  have hwB : c₀.kind.isSolid = false → c₀.endB = c₀.x := by
    intro hs
    have : c₀.kind.isWeight = true := by
      rcases hpm with ⟨h, -⟩ | ⟨h, -⟩ <;> rcases h with h | h | h <;>
        simp_all [Kind.isSolid, Kind.isWeight]
    simp [Comp.endB, this]
  have hbS : c₀.kind.isSolid = true → c₀.endB = c₀.y := by
    intro hs
    have : c₀.kind.isWeight = false := by
      revert hs; cases c₀.kind <;> simp [Kind.isSolid, Kind.isWeight]
    simp [Comp.endB, this]
  have hs1 : 1 ≤ (2 - c₀.kind.ord).toNat := by rcases hord with h | h <;> simp [h]
  have hpm' : (ps = [mkC (.G .plus) (liftA 1 c₀.x) (newA 0), mkC (.G .plus) (liftA 1 x)
      (liftA 1 c₀.endB)]) ∨ (ps = [mkC (.G .minus) (liftA 1 c₀.x) (liftA 1 x),
      mkC (.G .minus) (newA 0) (liftA 1 c₀.endB)]) := by
    rcases hpm with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · left
      rw [solidC_of_ne (by simp), solidC_of_ne (by simpa using cb.symm)]
    · right
      rw [solidC_of_ne (by simpa using cx), solidC_of_ne (by simp)]
  refine termOKS_mk sw (K := K) (R := [e, e', c₀]) lab
    (ps ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)])
    [mkC (.waved .s) (liftA 1 x) (newA 0)] co (2 - c₀.kind.ord).toNat hK ?_
    (List.Perm.of_eq (by simp [List.append_assoc]))
    (by simp [mkC, Kind.isRandom]) ?_ ?_ ?_ ?_ (fun a b => a == liftA 1 e'.x && b == liftA 1 x) ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · simp [hf1, Kind.isRandom]
    · simp [hf4, Kind.isRandom]
    · exact hr₀
  · -- new components
    intro c hc
    rw [List.mem_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact ⟨dPieces_newOK hps c hc, by
        rcases hpm with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
          (simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
           rcases hc with rfl | rfl <;> exact newOK_label.2 _ _ _)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ⟨NewOK_G _ (by simp), rfl⟩
      · exact ⟨NewOK_G _ (by simpa using hf6), rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      exact ⟨NewOK_waved _ _ _, rfl⟩
  · -- the atoms `kAt`
    intro c hc hr
    rw [List.mem_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · rcases hpm' with rfl | rfl <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
         rcases hc with rfl | rfl <;> (first
           | (apply kAt_G_of <;> intro _ <;> (try simp only [isRight_liftA, isRight_newA]) <;>
               solve_by_elim)
           | (apply kAt_ns_of (by simp [mkC, Kind.isSolid]) <;>
               (try simp only [mkC, isRight_liftA, isRight_newA]) <;> solve_by_elim)
           | (simp [mkC, Kind.isRandom] at *; done)))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> (first
        | (apply kAt_G_of <;> intro _ <;> (try simp only [isRight_liftA, isRight_newA]) <;>
            solve_by_elim)
        | (apply kAt_ns_of (by simp [mkC, Kind.isSolid]) <;>
            (try simp only [mkC, isRight_liftA, isRight_newA]) <;> solve_by_elim)
        | (simp [mkC, Kind.isRandom] at *; done))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp [mkC, Kind.isRandom] at hr
  · -- order
    have e1 : (Kind.G Charge.plus).ord = 1 := rfl
    have hR : ordL [e, e', c₀] = 2 + c₀.kind.ord := by
      simp only [ordL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hf1, hf4, e1]
      ring
    have hN : ordL (ps ++ [mkC (.G .plus) (newA 0) (liftA 1 e.y),
        mkC (.G .plus) (liftA 1 e'.x) (liftA 1 x)] ++ [mkC (.waved .s) (liftA 1 x) (newA 0)]) = 6 := by
      rcases hpm' with rfl | rfl <;> simp [ordL, mkC, Kind.ord] <;> norm_num
    rw [hN, hR]
    rcases hord with h | h <;> rw [h] <;> norm_num
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rcases hpm' with rfl | rfl <;> simp [mkC, Kind.isSolid, atB]
  · intro c hc hex
    simp only [Bool.and_eq_true, beq_iff_eq] at hex
    exact ⟨e'.x, x, hex.1, hex.2, hy'x⟩
  · rcases hpm' with rfl | rfl
    · simp [mkC, Kind.isSolid, hf6.symm]
      omega
    · simp only [List.cons_append, List.nil_append, List.filter_cons, mkC, Kind.isSolid,
        isNewA_liftA', isNewA_newA', beq_liftA, beq_self_eq_true, Bool.and_true, Bool.not_true,
        Bool.and_false, Bool.true_and, Bool.not_false, Bool.false_and, List.filter_nil,
        Bool.false_eq_true, ite_false]
      split_ifs <;> simp <;> omega
  · rcases hpm' with rfl | rfl <;> simp [mkC, Kind.isSolid]
  · intro h; omega
  · -- solid edges at external atoms
    have heS : (e.kind.isSolid && (e.x.isLeft || e.y.isLeft)) = e.y.isLeft := by
      simp [hf1, hf2, hxL, Kind.isSolid]
    have he'S : (e'.kind.isSolid && (e'.x.isLeft || e'.y.isLeft)) = e'.x.isLeft := by
      simp [hf4, hf5, hxL, Kind.isSolid]
    have hone : c₀.x.isLeft = false ∨ c₀.endB.isLeft = false := by
      cases sw
      · left; have := cxR.1 rfl; cases h : c₀.x <;> simp_all
      · right; have := cxR.2 rfl; cases h : c₀.endB <;> simp_all
    by_cases hcs : c₀.kind.isSolid = true
    · have hc : (c₀.kind.isSolid && (c₀.x.isLeft || c₀.y.isLeft)) =
          (c₀.x.isLeft || c₀.y.isLeft) := by simp [hcs]
      rw [hbS hcs] at hpm' hone
      rcases hone with h | h <;> rcases hpm' with rfl | rfl <;>
        (simp only [List.filter_cons, List.filter_nil, heS, he'S, hc, List.cons_append,
          List.nil_append]
         simp [mkC, Kind.isSolid, hxL, h]
         try (split_ifs <;> simp))
    · have hc : (c₀.kind.isSolid && (c₀.x.isLeft || c₀.y.isLeft)) = false := by
        simp at hcs; simp [hcs]
      have hb : c₀.endB = c₀.x := hwB (by simpa using hcs)
      rw [hb] at hpm' hone
      have hcL : c₀.x.isLeft = false := by rcases hone with h | h <;> exact h
      rcases hpm' with rfl | rfl <;>
        (simp only [List.filter_cons, List.filter_nil, heS, he'S, hc, List.cons_append,
          List.nil_append]
         simp [mkC, Kind.isSolid, hxL, hcL]
         try (split_ifs <;> simp))
  · intro _ h; omega
  · intro hl
    obtain ⟨u, rfl⟩ := Option.ne_none_iff_exists'.1 hl
    refine ⟨(mkC (.G .plus) (newA 0) (liftA 1 e.y)).labelQ u, ?_, ?_⟩
    · apply List.mem_append_left
      simp only [labW, labelQs]
      exact List.mem_map_of_mem (by simp)
    · simp [Comp.labelQ, mkC, Kind.isRandom]
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact sameMol_of_waved (w := .s) (List.mem_append_right _ (List.mem_cons_self ..))
      (by simpa using hxR) rfl

/-- The basic facts of the `GG` expansion for the terms without derivative. -/
private theorem GGHyp.facts2 (H : GGHyp sw C x Γ i j e e') :
    x.isLeft = false ∧ (sw = false → e'.x.isLeft = false) ∧
    (e.kind.isSolid && (e.x.isLeft || e.y.isLeft)) = e.y.isLeft ∧
    (e'.kind.isSolid && (e'.x.isLeft || e'.y.isLeft)) = e'.x.isLeft ∧
    e.kind.isRandom = true ∧ e'.kind.isRandom = true ∧ e.kind.ord = 1 ∧ e'.kind.ord = 1 := by
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hy'R, hxR, -⟩ := H.facts
  have hxL : x.isLeft = false := by cases x <;> simp_all
  refine ⟨hxL, fun hsw => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hy'R hsw
    cases h : e'.x <;> simp_all
  all_goals simp [hf1, hf2, hf4, hf5, hxL, Kind.isSolid, Kind.isRandom, Kind.ord]

/-- Terms with one new atom `α`, the edges `G_{xy} G_{y'x}` replaced by new components `N`. -/
private theorem GGHyp.termN1 (H : GGHyp sw C x Γ i j e e') (lab : Option (Atom k (n + 1)))
    (N₁ N₂ : List (Comp (Atom k (n + 1)))) (co : Coeff) (s : ℕ) (cs : List (Comp (Atom k (n + 1))))
    (hcs : cs.Perm (labW lab (liftCs 1 (ggF Γ i j) ++ N₁) ++ N₂))
    (hN₂ : ∀ c ∈ N₂, c.kind.isRandom = false)
    (hNo : ∀ c ∈ N₁ ++ N₂, NewOK c ∧ c.label = none)
    (hNK : ∀ c ∈ N₁ ++ N₂, c.kind.isRandom = true → (kAt sw c).isRight = true)
    (hs : ordL (N₁ ++ N₂) = 4 + s)
    (two : ((N₁ ++ N₂).filter fun c => c.kind.isSolid && atB (newA 0) c).length ≤ 2)
    (old : ((N₁ ++ N₂).filter fun c => c.kind.isSolid && !isNewA n c.x && !isNewA n c.y).length = 0)
    (zero : ((N₁ ++ N₂).filter fun c => c.kind.isSolid).length ≤ 2)
    (hext : ((N₁ ++ N₂).filter fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length ≤
      (if e.y.isLeft then 1 else 0) + (if e'.x.isLeft then 1 else 0))
    (hphi : lab = none → s = 0 → (⟨cs, co⟩ : Graph k (n + 1)).phi + 3 ≤ Γ.phi)
    (hlab : lab ≠ none → ∃ c ∈ N₁, c.kind.isRandom = true)
    (att : mkC (.waved .s) (liftA 1 x) (newA 0) ∈ N₂ ∨ mkC (.waved .plus) (liftA 1 x) (newA 0) ∈ N₂) :
    TermOKS sw Γ x (t1 cs co) := by
  obtain ⟨-, -, -, -, -, -, -, hxR, -, -, hperm, -, -⟩ := H.facts
  obtain ⟨-, -, heS, he'S, her, he'r, -, -⟩ := H.facts2
  refine termOKS_mk sw (K := ggF Γ i j) (R := [e, e']) lab N₁ N₂ co s hperm
    (by simp [her, he'r]) hcs hN₂ hNo hNK (by
      rw [hs]; simp only [ordL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [(H.facts2).2.2.2.2.2.2.1, (H.facts2).2.2.2.2.2.2.2]; push_cast; ring)
    (fun i => by obtain rfl : i = 0 := Subsingleton.elim _ _; exact two)
    (fun _ _ => false) (by simp) ?_ (zero.trans (by norm_num)) (fun _ => zero) ?_
    (fun hl hs0 => (hphi hl hs0).trans' (Nat.add_le_add_left (by split_ifs <;> omega) _)) ?_ ?_
  · refine le_trans (length_filter_mono _ _ _ fun c _ h => ?_) ((le_of_eq old).trans (Nat.zero_le s))
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨⟨h.1.1.1, h.1.1.2⟩, h.1.2⟩
  · refine hext.trans ?_
    simp only [List.filter_cons, List.filter_nil, heS, he'S]
    split_ifs <;> simp
  · intro hl
    obtain ⟨c, hc, hr⟩ := hlab hl
    obtain ⟨u, rfl⟩ := Option.ne_none_iff_exists'.1 hl
    refine ⟨c.labelQ u, hcs.mem_iff.2 (List.mem_append_left _ ?_), by simp [Comp.labelQ, hr]⟩
    simp only [labW, labelQs]
    exact List.mem_map_of_mem (List.mem_append_right _ hc)
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rcases att with h | h
    · exact sameMol_of_waved (g := ⟨cs, co⟩) (hcs.mem_iff.2 (List.mem_append_right _ h))
        (by simpa using hxR) rfl
    · exact sameMol_of_waved (g := ⟨cs, co⟩) (hcs.mem_iff.2 (List.mem_append_right _ h))
        (by simpa using hxR) rfl

/-- Terms with two new atoms `α`, `β`, the edges `G_{xy} G_{y'x}` replaced by new components. -/
private theorem GGHyp.termN2 (H : GGHyp sw C x Γ i j e e') (lab : Option (Atom k (n + 2)))
    (N₁ : List (Comp (Atom k (n + 2)))) (co : Coeff) (s : ℕ) (cs : List (Comp (Atom k (n + 2))))
    (hcs : cs.Perm (labW lab (liftCs 2 (ggF Γ i j) ++ N₁) ++
      [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)]))
    (hNo : ∀ c ∈ N₁ ++ [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)],
      NewOK c ∧ c.label = none)
    (hNK : ∀ c ∈ N₁ ++ [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)],
      c.kind.isRandom = true → (kAt sw c).isRight = true)
    (hs : ordL (N₁ ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)]) = 6 + s)
    (two : ∀ i : Fin 2, ((N₁ ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)]).filter fun c => c.kind.isSolid && atB (newA i) c).length ≤ 2)
    (old : ((N₁ ++ [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)]).filter
      fun c => c.kind.isSolid && !isNewA n c.x && !isNewA n c.y).length = 0)
    (zero : ((N₁ ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)]).filter fun c => c.kind.isSolid).length ≤ 2)
    (hext : ((N₁ ++ [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)]).filter
      fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length ≤
        (if e.y.isLeft then 1 else 0) + (if e'.x.isLeft then 1 else 0))
    (hphi : lab = none → s = 0 → (⟨cs, co⟩ : Graph k (n + 2)).phi + 3 ≤ Γ.phi)
    (hlab : lab ≠ none → ∃ c ∈ N₁, c.kind.isRandom = true) :
    TermOKS sw Γ x (t2 cs co) := by
  obtain ⟨-, -, -, -, -, -, -, hxR, -, -, hperm, -, -⟩ := H.facts
  obtain ⟨-, -, heS, he'S, her, he'r, h1, h2⟩ := H.facts2
  refine termOKS_mk sw (K := ggF Γ i j) (R := [e, e']) lab N₁
    [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)] co s hperm
    (by simp [her, he'r]) hcs (by simp [mkC, Kind.isRandom]) hNo hNK ?_ two
    (fun _ _ => false) (by simp) ?_ (zero.trans (by norm_num)) (fun _ => zero) ?_
    (fun hl hs0 => (hphi hl hs0).trans' (Nat.add_le_add_left (by split_ifs <;> omega) _)) ?_ ?_
  · rw [hs]; simp only [ordL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [h1, h2]; push_cast; ring
  · refine le_trans (length_filter_mono _ _ _ fun c _ h => ?_) ((le_of_eq old).trans (Nat.zero_le s))
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨⟨h.1.1.1, h.1.1.2⟩, h.1.2⟩
  · refine hext.trans ?_
    simp only [List.filter_cons, List.filter_nil, heS, he'S]
    split_ifs <;> simp
  · intro hl
    obtain ⟨c, hc, hr⟩ := hlab hl
    obtain ⟨u, rfl⟩ := Option.ne_none_iff_exists'.1 hl
    refine ⟨c.labelQ u, hcs.mem_iff.2 (List.mem_append_left _ ?_), by simp [Comp.labelQ, hr]⟩
    simp only [labW, labelQs]
    exact List.mem_map_of_mem (List.mem_append_right _ hc)
  · have hx : (liftA 2 x).isRight = true := by simpa using hxR
    have hmem1 : mkC (.waved .plus) (liftA 2 x) (newA 0) ∈ (⟨cs, co⟩ : Graph k (n + 2)).comps :=
      hcs.mem_iff.2 (List.mem_append_right _ (List.mem_cons_self ..))
    have hmem2 : mkC (.waved .s) (newA 0) (newA 1) ∈ (⟨cs, co⟩ : Graph k (n + 2)).comps :=
      hcs.mem_iff.2 (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have a0 := sameMol_of_waved hmem1 hx (isRight_newA _)
    have a1 := sameMol_of_waved hmem2 (isRight_newA _) (isRight_newA _)
    intro i
    fin_cases i
    · exact a0
    · exact (Graph.sameMol_equivalence _).trans a0 a1

/-- `m ∑_{α,β} S⁺_{xα} s_{αβ} (G_{ββ} - m) G_{αy} G_{y'α} f`. -/
private theorem GGHyp.term3 (H : GGHyp sw C x Γ i j e e') (co : Coeff) :
    TermOKS sw Γ x (t2 (liftCs 2 (ggF Γ i j) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 1) (newA 1),
      mkC (.G .plus) (newA 0) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) co) := by
  obtain ⟨-, -, -, -, -, -, hy'R, hxR, -, -, -, -, -⟩ := H.facts
  have heyR := H.eyR
  refine H.termN2 none [mkC (.light .plus) (newA 1) (newA 1), mkC (.G .plus) (newA 0) (liftA 2 e.y),
    mkC (.G .plus) (liftA 2 e'.x) (newA 0)] co 1 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun _ h => by simp at h)
    (fun h => absurd rfl h)
  · simp only [labW, List.append_assoc]
    exact List.Perm.append_left _ (List.perm_append_comm (l₁ := [_, _]) (l₂ := [_, _, _]))
  · intro c hc
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact ⟨NewOK_light _ _, rfl⟩
    · exact ⟨NewOK_G _ (by simp), rfl⟩
    · exact ⟨NewOK_G _ (by simp), rfl⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
  · intro c hc hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      (first
        | (apply kAt_G_of <;> intro _ <;> (try simp only [isRight_liftA, isRight_newA]) <;>
            solve_by_elim)
        | (apply kAt_ns_of (by simp [mkC, Kind.isSolid]) <;>
            (try simp only [mkC, isRight_liftA, isRight_newA]) <;> solve_by_elim)
        | (simp [mkC, Kind.isRandom] at *; done))
  · simp [ordL, mkC, Kind.ord]; try norm_num
  · intro i; fin_cases i <;> simp [mkC, Kind.isSolid, atB]
  · simp [mkC, Kind.isSolid]
  · simp [mkC, Kind.isSolid]
  · simp [List.filter_cons, mkC, Kind.isSolid]
    split_ifs <;> simp

end GGFam2

section GGFam3

variable {k n : ℕ} {sw : Bool} {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k n)}

/-- `m ∑_α (G_{xx} - m) s_{xα} G_{αy} G_{y'α} f`. -/
private theorem GGHyp.term4 (H : GGHyp sw C x Γ i j e e') (co : Coeff) :
    TermOKS sw Γ x (t1 (liftCs 1 (ggF Γ i j) ++ [mkC (.light .plus) (liftA 1 x) (liftA 1 x),
      mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 e.y),
      mkC (.G .plus) (liftA 1 e'.x) (newA 0)]) co) := by
  obtain ⟨-, -, -, -, -, -, hy'R, hxR, -, -, -, -, -⟩ := H.facts
  have heyR := H.eyR
  refine H.termN1 none [mkC (.light .plus) (liftA 1 x) (liftA 1 x),
    mkC (.G .plus) (newA 0) (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x) (newA 0)]
    [mkC (.waved .s) (liftA 1 x) (newA 0)] co 1 _ ?_ (by simp [mkC, Kind.isRandom]) ?_ ?_ ?_ ?_ ?_
    ?_ ?_ (fun _ h => by simp at h) (fun h => absurd rfl h) (Or.inl (List.mem_singleton_self _))
  · simp only [labW, List.append_assoc]
    exact List.Perm.append_left _ (List.Perm.cons _
      (List.perm_append_comm (l₁ := [_]) (l₂ := [_, _])))
  · intro c hc
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨NewOK_light _ _, rfl⟩
    · exact ⟨NewOK_G _ (by simp), rfl⟩
    · exact ⟨NewOK_G _ (by simp), rfl⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
  · intro c hc hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;>
      (first
        | (apply kAt_G_of <;> intro _ <;> (try simp only [isRight_liftA, isRight_newA]) <;>
            solve_by_elim)
        | (apply kAt_ns_of (by simp [mkC, Kind.isSolid]) <;>
            (try simp only [mkC, isRight_liftA, isRight_newA]) <;> solve_by_elim)
        | (simp [mkC, Kind.isRandom] at *; done))
  · simp [ordL, mkC, Kind.ord]; try norm_num
  · simp [mkC, Kind.isSolid, atB]
  · simp [mkC, Kind.isSolid]
  · simp [mkC, Kind.isSolid]
  · simp [List.filter_cons, mkC, Kind.isSolid]
    split_ifs <;> simp

/-- `m ∑_{α,β} S⁺_{xα} s_{αβ} (G_{αα} - m) G_{βy} G_{y'β} f`. -/
private theorem GGHyp.term5 (H : GGHyp sw C x Γ i j e e') (co : Coeff) :
    TermOKS sw Γ x (t2 (liftCs 2 (ggF Γ i j) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
      mkC (.G .plus) (newA 1) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 1)]) co) := by
  obtain ⟨-, -, -, -, -, -, hy'R, hxR, -, -, -, -, -⟩ := H.facts
  have heyR := H.eyR
  refine H.termN2 none [mkC (.light .plus) (newA 0) (newA 0), mkC (.G .plus) (newA 1) (liftA 2 e.y),
    mkC (.G .plus) (liftA 2 e'.x) (newA 1)] co 1 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun _ h => by simp at h)
    (fun h => absurd rfl h)
  · simp only [labW, List.append_assoc]
    exact List.Perm.append_left _ (List.perm_append_comm (l₁ := [_, _]) (l₂ := [_, _, _]))
  · intro c hc
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact ⟨NewOK_light _ _, rfl⟩
    · exact ⟨NewOK_G _ (by simp), rfl⟩
    · exact ⟨NewOK_G _ (by simp), rfl⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
  · intro c hc hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      (first
        | (apply kAt_G_of <;> intro _ <;> (try simp only [isRight_liftA, isRight_newA]) <;>
            solve_by_elim)
        | (apply kAt_ns_of (by simp [mkC, Kind.isSolid]) <;>
            (try simp only [mkC, isRight_liftA, isRight_newA]) <;> solve_by_elim)
        | (simp [mkC, Kind.isRandom] at *; done))
  · simp [ordL, mkC, Kind.ord]; try norm_num
  · intro i; fin_cases i <;> simp [mkC, Kind.isSolid, atB]
  · simp [mkC, Kind.isSolid]
  · simp [mkC, Kind.isSolid]
  · simp [List.filter_cons, mkC, Kind.isSolid]
    split_ifs <;> simp

/-- The `Q`-term `Q_α (G_{αy} G_{y'α} f) S⁺_{xα}`. -/
private theorem GGHyp.termQ2 (H : GGHyp sw C x Γ i j e e') (co : Coeff) :
    TermOKS sw Γ x (t1 (labelQs (newA 0) (liftCs 1 (ggF Γ i j) ++ [mkC (.G .plus) (newA 0)
      (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x) (newA 0)]) ++
      [mkC (.waved .plus) (liftA 1 x) (newA 0)]) co) := by
  obtain ⟨-, -, -, -, -, -, hy'R, hxR, -, -, -, -, -⟩ := H.facts
  have heyR := H.eyR
  refine H.termN1 (some (newA 0)) [mkC (.G .plus) (newA 0) (liftA 1 e.y),
    mkC (.G .plus) (liftA 1 e'.x) (newA 0)] [mkC (.waved .plus) (liftA 1 x) (newA 0)] co 0 _
    (List.Perm.refl _) (by simp [mkC, Kind.isRandom]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun h => by simp at h)
    (fun _ => ⟨_, List.mem_cons_self .., rfl⟩) (Or.inr (List.mem_singleton_self _))
  · intro c hc
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨NewOK_G _ (by simp), rfl⟩
    · exact ⟨NewOK_G _ (by simp), rfl⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
  · intro c hc hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      (first
        | (apply kAt_G_of <;> intro _ <;> (try simp only [isRight_liftA, isRight_newA]) <;>
            solve_by_elim)
        | (apply kAt_ns_of (by simp [mkC, Kind.isSolid]) <;>
            (try simp only [mkC, isRight_liftA, isRight_newA]) <;> solve_by_elim)
        | (simp [mkC, Kind.isRandom] at *; done))
  · simp [ordL, mkC, Kind.ord]; try norm_num
  · simp [mkC, Kind.isSolid, atB]
  · simp [mkC, Kind.isSolid]
  · simp [mkC, Kind.isSolid]
  · simp [List.filter_cons, mkC, Kind.isSolid]
    split_ifs <;> simp

/-- The `Q`-term `Q_α (G_{ββ} - m)(G_{αy} G_{y'α} f) S⁺_{xα} s_{αβ}`. -/
private theorem GGHyp.termQ5 (H : GGHyp sw C x Γ i j e e') (co : Coeff) :
    TermOKS sw Γ x (t2 (labelQs (newA 0) (liftCs 2 (ggF Γ i j) ++ [mkC (.light .plus) (newA 1) (newA 1),
      mkC (.G .plus) (newA 0) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) ++
      [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)]) co) := by
  obtain ⟨-, -, -, -, -, -, hy'R, hxR, -, -, -, -, -⟩ := H.facts
  have heyR := H.eyR
  refine H.termN2 (some (newA 0)) [mkC (.light .plus) (newA 1) (newA 1),
    mkC (.G .plus) (newA 0) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 0)] co 1 _
    (List.Perm.refl _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun h => by simp at h)
    (fun _ => ⟨_, List.mem_cons_self .., rfl⟩)
  · intro c hc
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact ⟨NewOK_light _ _, rfl⟩
    · exact ⟨NewOK_G _ (by simp), rfl⟩
    · exact ⟨NewOK_G _ (by simp), rfl⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
  · intro c hc hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      (first
        | (apply kAt_G_of <;> intro _ <;> (try simp only [isRight_liftA, isRight_newA]) <;>
            solve_by_elim)
        | (apply kAt_ns_of (by simp [mkC, Kind.isSolid]) <;>
            (try simp only [mkC, isRight_liftA, isRight_newA]) <;> solve_by_elim)
        | (simp [mkC, Kind.isRandom] at *; done))
  · simp [ordL, mkC, Kind.ord]; try norm_num
  · intro i; fin_cases i <;> simp [mkC, Kind.isSolid, atB]
  · simp [mkC, Kind.isSolid]
  · simp [mkC, Kind.isSolid]
  · simp [List.filter_cons, mkC, Kind.isSolid]
    split_ifs <;> simp

/-- The `Q`-term `-m Q_x (G_{xx} G_{αy} G_{y'α} f) s_{xα}`. -/
private theorem GGHyp.termQ6 (H : GGHyp sw C x Γ i j e e') (co : Coeff) :
    TermOKS sw Γ x (t1 (labelQs (liftA 1 x) (liftCs 1 (ggF Γ i j) ++ [mkC (.weight .plus) (liftA 1 x)
      (liftA 1 x), mkC (.G .plus) (newA 0) (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x) (newA 0)]) ++
      [mkC (.waved .s) (liftA 1 x) (newA 0)]) co) := by
  obtain ⟨-, -, -, -, -, -, hy'R, hxR, -, -, -, -, -⟩ := H.facts
  have heyR := H.eyR
  refine H.termN1 (some (liftA 1 x)) [mkC (.weight .plus) (liftA 1 x) (liftA 1 x),
    mkC (.G .plus) (newA 0) (liftA 1 e.y), mkC (.G .plus) (liftA 1 e'.x) (newA 0)]
    [mkC (.waved .s) (liftA 1 x) (newA 0)] co 0 _
    (List.Perm.refl _) (by simp [mkC, Kind.isRandom]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun h => by simp at h)
    (fun _ => ⟨_, List.mem_cons_self .., rfl⟩) (Or.inl (List.mem_singleton_self _))
  · intro c hc
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨NewOK_weight _ _, rfl⟩
    · exact ⟨NewOK_G _ (by simp), rfl⟩
    · exact ⟨NewOK_G _ (by simp), rfl⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
  · intro c hc hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;>
      (first
        | (apply kAt_G_of <;> intro _ <;> (try simp only [isRight_liftA, isRight_newA]) <;>
            solve_by_elim)
        | (apply kAt_ns_of (by simp [mkC, Kind.isSolid]) <;>
            (try simp only [mkC, isRight_liftA, isRight_newA]) <;> solve_by_elim)
        | (simp [mkC, Kind.isRandom] at *; done))
  · simp [ordL, mkC, Kind.ord]; try norm_num
  · simp [mkC, Kind.isSolid, atB]
  · simp [mkC, Kind.isSolid]
  · simp [mkC, Kind.isSolid]
  · simp [List.filter_cons, mkC, Kind.isSolid]
    split_ifs <;> simp

/-- The `Q`-term `-m Q_α (G_{αα} G_{βy} G_{y'β} f) S⁺_{xα} s_{αβ}`. -/
private theorem GGHyp.termQ7 (H : GGHyp sw C x Γ i j e e') (co : Coeff) :
    TermOKS sw Γ x (t2 (labelQs (newA 0) (liftCs 2 (ggF Γ i j) ++ [mkC (.weight .plus) (newA 0) (newA 0),
      mkC (.G .plus) (newA 1) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 1)]) ++
      [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)]) co) := by
  obtain ⟨-, -, -, -, -, -, hy'R, hxR, -, -, -, -, -⟩ := H.facts
  have heyR := H.eyR
  refine H.termN2 (some (newA 0)) [mkC (.weight .plus) (newA 0) (newA 0),
    mkC (.G .plus) (newA 1) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 1)] co 0 _
    (List.Perm.refl _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun h => by simp at h)
    (fun _ => ⟨_, List.mem_cons_self .., rfl⟩)
  · intro c hc
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact ⟨NewOK_weight _ _, rfl⟩
    · exact ⟨NewOK_G _ (by simp), rfl⟩
    · exact ⟨NewOK_G _ (by simp), rfl⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
  · intro c hc hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;>
      (first
        | (apply kAt_G_of <;> intro _ <;> (try simp only [isRight_liftA, isRight_newA]) <;>
            solve_by_elim)
        | (apply kAt_ns_of (by simp [mkC, Kind.isSolid]) <;>
            (try simp only [mkC, isRight_liftA, isRight_newA]) <;> solve_by_elim)
        | (simp [mkC, Kind.isRandom] at *; done))
  · simp [ordL, mkC, Kind.ord]; try norm_num
  · intro i; fin_cases i <;> simp [mkC, Kind.isSolid, atB]
  · simp [mkC, Kind.isSolid]
  · simp [mkC, Kind.isSolid]
  · simp [List.filter_cons, mkC, Kind.isSolid]
    split_ifs <;> simp

end GGFam3

section GGFam4

variable {k n : ℕ} {sw : Bool} {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k n)}

@[simp] private theorem isNewA_self (u : Atom k n) : isNewA n u = false := by
  rcases u with a | a <;> simp [isNewA]

/-- The `Q`-term `Q_x 𝒢`. -/
private theorem termQx {x : Atom k n} {Γ : Graph k n} (hx : x.isRight = true)
    (hr : ∃ c ∈ Γ.comps, c.kind.isRandom = true) (co : Coeff) :
    TermOKS sw Γ x ⟨n, ⟨labelQs x Γ.comps, co⟩, id⟩ := by
  rw [tracked_id_eq]
  refine termOKS_mk sw (j := 0) (K := Γ.comps) (R := []) (some x) [] [] co 0 (by simp) (by simp)
    (List.Perm.of_eq (by simp [labW, liftCs_zero])) (by simp) (by simp) (by simp) (by simp [ordL])
    (fun i => i.elim0) (fun _ _ => false) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun h => by simp at h) ?_ (fun i => i.elim0)
  intro _
  obtain ⟨c, hc, hrc⟩ := hr
  exact ⟨c.labelQ x, List.mem_map_of_mem hc, by simp [Comp.labelQ, hrc]⟩

/-- The `Q`-term `-m Q_x ((G_{αα} - m) 𝒢) s_{xα}`. -/
private theorem termQxl {x : Atom k n} {Γ : Graph k n} (hx : x.isRight = true) (co : Coeff) :
    TermOKS sw Γ x (t1 (labelQs (liftA 1 x) (liftCs 1 Γ.comps ++ [mkC (.light .plus) (newA 0) (newA 0)]) ++
      [mkC (.waved .s) (liftA 1 x) (newA 0)]) co) := by
  refine termOKS_mk sw (K := Γ.comps) (R := []) (some (liftA 1 x))
    [mkC (.light .plus) (newA 0) (newA 0)] [mkC (.waved .s) (liftA 1 x) (newA 0)] co 1 (by simp)
    (by simp) (List.Perm.refl _) (by simp [mkC, Kind.isRandom]) ?_ ?_ (by simp [ordL, mkC, Kind.ord])
    (fun i => by simp [mkC, Kind.isSolid]) (fun _ _ => false) (by simp) (by simp [mkC, Kind.isSolid])
    (by simp [mkC, Kind.isSolid]) (by simp [mkC, Kind.isSolid]) (by simp [mkC, Kind.isSolid])
    (fun h => by simp at h) ?_ ?_
  · intro c hc
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨NewOK_light _ _, rfl⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
  · intro c hc hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
      (first
        | (apply kAt_G_of <;> intro _ <;> (try simp only [isRight_liftA, isRight_newA]) <;>
            solve_by_elim)
        | (apply kAt_ns_of (by simp [mkC, Kind.isSolid]) <;>
            (try simp only [mkC, isRight_liftA, isRight_newA]) <;> solve_by_elim)
        | (simp [mkC, Kind.isRandom] at *; done))
  · intro _
    exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem (List.mem_append_right _
      (List.mem_singleton_self _))), by simp [Comp.labelQ, mkC, Kind.isRandom]⟩
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact sameMol_of_waved (List.mem_append_right _ (List.mem_singleton_self _))
      (by simpa using hx) rfl

/-- The main term `m S⁺_{xy} G_{y'y} f` and its `Q`-term `-m Q_y(G_{y'y} f) S⁺_{xy}`. -/
private theorem GGHyp.termMain (H : GGHyp sw C x Γ i j e e') (lab : Option (Atom k n))
    (hlab : lab = none ∨ lab = some e.y) (co : Coeff)
    (hphi : lab = none → e'.x = e.y → (⟨labW lab (ggMain Γ i j e e') ++
      [mkC (.waved .plus) x e.y], co⟩ : Graph k n).phi + 3 ≤ Γ.phi) :
    TermOKS sw Γ x ⟨n, ⟨labW lab (ggMain Γ i j e e') ++ [mkC (.waved .plus) x e.y], co⟩, id⟩ := by
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hy'R, hxR, -, -, hperm, -, -⟩ := H.facts
  obtain ⟨hxL, hy'L, heS, he'S, her, he'r, h1, h2⟩ := H.facts2
  rw [tracked_id_eq]
  have hsC : (solidC .plus e'.x e.y).kind.ord = if e'.x = e.y then 0 else 1 := ord_solidC _ _ _
  refine termOKS_mk sw (j := 0) (K := ggF Γ i j) (R := [e, e']) lab [solidC .plus e'.x e.y]
    [mkC (.waved .plus) x e.y] co (if e'.x = e.y then 0 else 1) hperm (by simp [her, he'r])
    (List.Perm.of_eq (by simp [ggMain, liftCs_zero])) (by simp [mkC, Kind.isRandom]) ?_ ?_ ?_
    (fun i => i.elim0) (fun _ _ => false) (by simp) ?_ ?_ ?_ ?_ ?_ ?_ (fun i => i.elim0)
  · intro c hc
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨NewOK_solidC _ _ _, newOK_label.2 _ _ _⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
  · intro c hc hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · by_cases hyy : e'.x = e.y
      · rw [hyy, solidC_self]
        apply kAt_ns_of (by simp [mkC, Kind.isSolid])
        cases sw
        · simpa [mkC, hyy] using hy'R rfl
        · simpa [mkC] using H.eyR rfl
      · rw [solidC_of_ne hyy]
        exact kAt_G_of hy'R H.eyR
    · simp [mkC, Kind.isRandom] at hr
  · simp only [ordL, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, hsC, h1, h2]
    split_ifs <;> simp [mkC, Kind.ord] <;> norm_num
  · by_cases hyy : e'.x = e.y
    · rw [hyy, solidC_self]; simp [mkC, Kind.isSolid]
    · rw [solidC_of_ne hyy]; simp [mkC, Kind.isSolid, hyy]
  · by_cases hyy : e'.x = e.y
    · rw [hyy, solidC_self]; simp [mkC, Kind.isSolid]
    · rw [solidC_of_ne hyy]; simp [mkC, Kind.isSolid]
  · by_cases hyy : e'.x = e.y
    · intro _; rw [hyy, solidC_self]; simp [mkC, Kind.isSolid]
    · intro _; rw [solidC_of_ne hyy]; simp [mkC, Kind.isSolid]
  · by_cases hyy : e'.x = e.y
    · rw [hyy, solidC_self]; simp [List.filter_cons, mkC, Kind.isSolid, heS, he'S]
    · rw [solidC_of_ne hyy]
      simp only [List.filter_cons, List.filter_nil, heS, he'S]
      by_cases hyL : e.y.isLeft = true
      · simp only [List.singleton_append, List.cons_append, List.nil_append]
        rw [List.filter_cons_of_pos (by simp [mkC, Kind.isSolid, hyL]),
          List.filter_cons_of_neg (by simp [mkC, Kind.isSolid])]
        simp [hyL]
        try (split_ifs <;> simp)
      · simp only [List.singleton_append, List.cons_append, List.nil_append, List.filter_cons,
          List.filter_nil]
        split_ifs <;> rcases hy : e.y with a | a <;> simp_all [mkC, Kind.isSolid]
  · intro hl hs0
    have hyy : e'.x = e.y := by split_ifs at hs0 with h; exact h
    exact (hphi hl hyy).trans' (Nat.add_le_add_left (by split_ifs <;> omega) _)
  · intro hl
    rcases hlab with h | h
    · exact absurd h hl
    · subst h
      exact ⟨(solidC .plus e'.x e.y).labelQ e.y, List.mem_append_left _ (List.mem_map_of_mem
        (List.mem_append_right _ (List.mem_singleton_self _))), by
        unfold solidC Comp.labelQ; split_ifs <;> simp [mkC, Kind.isRandom]⟩

end GGFam4

section GGFam5

variable {k n : ℕ} {sw : Bool} {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k n)}

/-- The derivative terms of `f` at `β`, without or with the label `Q_α`. -/
private theorem GGHyp.termD2 (H : GGHyp sw C x Γ i j e e') {d : List (Comp (Atom k (n + 2)))}
    (hd : d ∈ ggD2 Γ i j e e') (lab : Option (Atom k (n + 2))) (co : Coeff) :
    TermOKS sw Γ x (t2 (labW lab d ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)]) co) := by
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hy'R, hxR, -, hy'x, hperm, -, -⟩ := H.facts
  obtain ⟨hxL, -, heS, he'S, -, -, h1, h2⟩ := H.facts2
  have heyR := H.eyR
  unfold ggD2 at hd
  obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
  obtain ⟨c₀, K, ps, hF, hc₀, hps, rfl⟩ := dTerms_lift_split hd₀
  have hpm := dPieces_lift hps
  have hr₀ : c₀.kind.isRandom = true := by
    rcases hpm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact (kind_ord_of_pm h).2.2
  obtain ⟨cx, cb, cxR, -⟩ := H.f_rand hc₀ hr₀
  have cxR1 := cxR.1
  have cxR2 := cxR.2
  have hone : c₀.x.isLeft = false ∨ c₀.endB.isLeft = false := by
    cases sw
    · left; have := cxR.1 rfl; cases h : c₀.x <;> simp_all
    · right; have := cxR.2 rfl; cases h : c₀.endB <;> simp_all
  have hK : Γ.comps.Perm (K ++ [e, e', c₀]) := by
    refine hperm.trans ?_
    refine (hF.append_right _).trans ?_
    rw [List.append_assoc]
    exact List.Perm.append_left K (List.perm_append_comm (l₁ := [c₀]) (l₂ := [e, e']))
  have hord : c₀.kind.ord = 1 ∨ c₀.kind.ord = 0 := by
    rcases hpm with ⟨h, -⟩ | ⟨h, -⟩
    · rcases h with h | h | h <;> exact (kind_ord_of_pm (ch := .plus) (by simp [h])).1
    · rcases h with h | h | h <;> exact (kind_ord_of_pm (ch := .minus) (by simp [h])).1
  have hwB : c₀.kind.isSolid = false → c₀.endB = c₀.x := by
    intro hs
    have : c₀.kind.isWeight = true := by
      rcases hpm with ⟨h, -⟩ | ⟨h, -⟩ <;> rcases h with h | h | h <;>
        simp_all [Kind.isSolid, Kind.isWeight]
    simp [Comp.endB, this]
  have hbS : c₀.kind.isSolid = true → c₀.endB = c₀.y := by
    intro hs
    have : c₀.kind.isWeight = false := by
      revert hs; cases c₀.kind <;> simp [Kind.isSolid, Kind.isWeight]
    simp [Comp.endB, this]
  have hs1 : 1 ≤ (2 - c₀.kind.ord).toNat := by rcases hord with h | h <;> simp [h]
  have hpm' : (ps = [mkC (.G .plus) (liftA 2 c₀.x) (newA 1), mkC (.G .plus) (newA 0)
      (liftA 2 c₀.endB)]) ∨ (ps = [mkC (.G .minus) (liftA 2 c₀.x) (newA 0),
      mkC (.G .minus) (newA 1) (liftA 2 c₀.endB)]) := by
    rcases hpm with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · left
      rw [solidC_of_ne (by simp), solidC_of_ne (by simp)]
    · right
      rw [solidC_of_ne (by simp), solidC_of_ne (by simp)]
  refine termOKS_mk sw (K := K) (R := [e, e', c₀]) lab
    (ps ++ [mkC (.G .plus) (newA 1) (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 0)])
    [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)] co
    (2 - c₀.kind.ord).toNat hK ?_ (List.Perm.of_eq (by simp [List.append_assoc]))
    (by simp [mkC, Kind.isRandom]) ?_ ?_ ?_ ?_ (fun _ _ => false) (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · simp [hf1, Kind.isRandom]
    · simp [hf4, Kind.isRandom]
    · exact hr₀
  · intro c hc
    rw [List.mem_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact ⟨dPieces_newOK hps c hc, by
        rcases hpm' with rfl | rfl <;>
          (simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
           rcases hc with rfl | rfl <;> rfl)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ⟨NewOK_G _ (by simp), rfl⟩
      · exact ⟨NewOK_G _ (by simp), rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ⟨NewOK_waved _ _ _, rfl⟩
      · exact ⟨NewOK_waved _ _ _, rfl⟩
  · intro c hc hr
    rw [List.mem_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · rcases hpm' with rfl | rfl <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
         rcases hc with rfl | rfl <;> (first
           | (apply kAt_G_of <;> intro _ <;> (try simp only [isRight_liftA, isRight_newA]) <;>
               solve_by_elim)
           | (apply kAt_ns_of (by simp [mkC, Kind.isSolid]) <;>
               (try simp only [mkC, isRight_liftA, isRight_newA]) <;> solve_by_elim)
           | (simp [mkC, Kind.isRandom] at *; done)))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> (first
        | (apply kAt_G_of <;> intro _ <;> (try simp only [isRight_liftA, isRight_newA]) <;>
            solve_by_elim)
        | (apply kAt_ns_of (by simp [mkC, Kind.isSolid]) <;>
            (try simp only [mkC, isRight_liftA, isRight_newA]) <;> solve_by_elim)
        | (simp [mkC, Kind.isRandom] at *; done))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [mkC, Kind.isRandom] at hr
  · have e1 : (Kind.G Charge.plus).ord = 1 := rfl
    have hR : ordL [e, e', c₀] = 2 + c₀.kind.ord := by
      simp only [ordL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h1, h2]
      ring
    have hN : ordL (ps ++ [mkC (.G .plus) (newA 1) (liftA 2 e.y),
        mkC (.G .plus) (liftA 2 e'.x) (newA 0)] ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1)]) = 8 := by
      rcases hpm' with rfl | rfl <;> simp [ordL, mkC, Kind.ord] <;> norm_num
    rw [hN, hR]
    rcases hord with h | h <;> rw [h] <;> norm_num
  · intro i
    rcases hpm' with rfl | rfl <;> fin_cases i <;> simp [mkC, Kind.isSolid, atB]
  · rcases hpm' with rfl | rfl <;> simp [mkC, Kind.isSolid]
  · rcases hpm' with rfl | rfl <;> simp [mkC, Kind.isSolid]
  · intro h; omega
  · by_cases hcs : c₀.kind.isSolid = true
    · have hc : (c₀.kind.isSolid && (c₀.x.isLeft || c₀.y.isLeft)) =
          (c₀.x.isLeft || c₀.y.isLeft) := by simp [hcs]
      rw [hbS hcs] at hpm' hone
      rcases hone with h | h <;> rcases hpm' with rfl | rfl <;>
        (simp only [List.filter_cons, List.filter_nil, heS, he'S, hc, List.cons_append,
          List.nil_append]
         simp [mkC, Kind.isSolid, hxL, h]
         try (split_ifs <;> simp))
    · have hc : (c₀.kind.isSolid && (c₀.x.isLeft || c₀.y.isLeft)) = false := by
        simp at hcs; simp [hcs]
      have hb : c₀.endB = c₀.x := hwB (by simpa using hcs)
      rw [hb] at hpm' hone
      have hcL : c₀.x.isLeft = false := by rcases hone with h | h <;> exact h
      rcases hpm' with rfl | rfl <;>
        (simp only [List.filter_cons, List.filter_nil, heS, he'S, hc, List.cons_append,
          List.nil_append]
         simp [mkC, Kind.isSolid, hxL, hcL]
         try (split_ifs <;> simp))
  · intro _ h; omega
  · intro hl
    obtain ⟨u, rfl⟩ := Option.ne_none_iff_exists'.1 hl
    refine ⟨(mkC (.G .plus) (newA 1) (liftA 2 e.y)).labelQ u, ?_, ?_⟩
    · apply List.mem_append_left
      simp only [labW, labelQs]
      exact List.mem_map_of_mem (by simp)
    · simp [Comp.labelQ, mkC, Kind.isRandom]
  · have hx : (liftA 2 x).isRight = true := by simpa using hxR
    have a0 := sameMol_of_waved (g := ⟨labW lab (liftCs 2 K ++ ps ++ [mkC (.G .plus) (newA 1)
      (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x)
      (newA 0), mkC (.waved .s) (newA 0) (newA 1)], co⟩)
      (List.mem_append_right _ (List.mem_cons_self ..)) hx (isRight_newA 0)
    have a1 := sameMol_of_waved (g := ⟨labW lab (liftCs 2 K ++ ps ++ [mkC (.G .plus) (newA 1)
      (liftA 2 e.y), mkC (.G .plus) (liftA 2 e'.x) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x)
      (newA 0), mkC (.waved .s) (newA 0) (newA 1)], co⟩)
      (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (isRight_newA 0)
      (isRight_newA 1)
    intro i
    fin_cases i
    · exact a0
    · exact (Graph.sameMol_equivalence _).trans a0 a1

end GGFam5

/-! ## The potential, atom by atom -/

section PhiLocal

variable {k n : ℕ}

/-- `1` for an atom of degree `2` that is not standard neutral. -/
private def badI {m : ℕ} (g : Graph k m) (u : Atom k m) : ℕ :=
  if g.deg u = 2 ∧ g.stdNeutralAt u = false then 1 else 0

private theorem badN_eq {m : ℕ} (g : Graph k m) : g.badN = ∑ i : Fin m, badI g (.inr i) := by
  unfold Graph.badN badI
  rw [Finset.card_filter]

private theorem degX_lift {j : ℕ} (g : Graph k (n + j)) : g.degX =
    ∑ i : Fin n, (g.deg (liftA j (.inr i)) - 2) + ∑ i : Fin j, (g.deg (newA i) - 2) := by
  unfold Graph.degX
  rw [Fin.sum_univ_add]
  rfl

private theorem badN_lift {j : ℕ} (g : Graph k (n + j)) : g.badN =
    ∑ i : Fin n, badI g (liftA j (.inr i)) + ∑ i : Fin j, badI g (newA i) := by
  rw [badN_eq, Fin.sum_univ_add]
  rfl

private theorem sum_two_eq {β : Type*} [AddCommMonoid β] (f g : Fin n → β) (a b : Fin n) (hab : a ≠ b)
    (h : ∀ i, i ≠ a → i ≠ b → f i = g i) :
    (∑ i, f i) + g a + g b = (∑ i, g i) + f a + f b := by
  have hb : b ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ hb,
    ← Finset.add_sum_erase _ g (Finset.mem_univ a), ← Finset.add_sum_erase _ g hb]
  rw [Finset.sum_congr rfl fun i hi => h i (Finset.mem_erase.1 (Finset.mem_erase.1 hi).2).1
    (Finset.mem_erase.1 hi).1]
  abel

private theorem sum_one_eq {β : Type*} [AddCommMonoid β] (f g : Fin n → β) (a : Fin n)
    (h : ∀ i, i ≠ a → f i = g i) : (∑ i, f i) + g a = (∑ i, g i) + f a := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ g (Finset.mem_univ a)]
  rw [Finset.sum_congr rfl fun i hi => h i (Finset.mem_erase.1 hi).1]
  abel

/-- An atom with two solid edges of the same charge, one leaving and one entering, is not standard
neutral. -/
private theorem std_false_same {m : ℕ} {g : Graph k m} {u : Atom k m} {c₁ c₂ : Comp (Atom k m)}
    {ch : Charge} (h₁ : c₁ ∈ g.comps) (h₂ : c₂ ∈ g.comps) (k₁ : c₁.kind = .G ch)
    (k₂ : c₂.kind = .G ch) (o₁ : c₁.x = u ∧ c₁.y ≠ u) (i₂ : c₂.y = u ∧ c₂.x ≠ u) :
    g.stdNeutralAt u = false := by
  by_contra hs
  rw [Bool.not_eq_false, std_eq] at hs
  simp only [Bool.and_eq_true] at hs
  have hm := hs.2
  have e1 : (true, ch) ∈ g.ends u := by
    unfold Graph.ends
    exact List.mem_filterMap.2 ⟨c₁, h₁, by simp [k₁, o₁.1, o₁.2]⟩
  have e2 : (false, ch) ∈ g.ends u := by
    unfold Graph.ends
    exact List.mem_filterMap.2 ⟨c₂, h₂, by simp [k₂, i₂.1, i₂.2]⟩
  revert hm e1 e2
  generalize g.ends u = l
  intro hm e1 e2
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp [stdM] at hm
  · simp [stdM] at hm
  · simp only [stdM, Bool.and_eq_true, bne_iff_ne, ne_eq] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at e1 e2
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    simp only [Prod.mk.injEq] at e1 e2 hm
    rcases e1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases e2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> simp_all
  · simp [stdM] at hm

end PhiLocal

section GGPhi

variable {k n : ℕ} {sw : Bool} {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k n)}

/-- The potential decreases at the main term `m S⁺_{xy} G_{yy} f` of `Ô_GG` when `y = y'`: the
atom `x` loses its two solid edges and `y` two of its solid edges. -/
private theorem GGHyp.phi_main (H : GGHyp sw C x Γ i j e e') (hyy : e'.x = e.y) (co : Coeff) :
    (⟨ggMain Γ i j e e' ++ [mkC (.waved .plus) x e.y], co⟩ : Graph k n).phi + 3 ≤ Γ.phi := by
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hy'R, hxR, -, -, hperm, he, he'⟩ := H.facts
  obtain ⟨-, -, -, -, her, he'r, -, -⟩ := H.facts2
  set g : Graph k n := ⟨ggMain Γ i j e e' ++ [mkC (.waved .plus) x e.y], co⟩ with hg
  have hS : Sch Γ 0 [e, e'] [solidC .plus e'.x e.y, mkC (.waved .plus) x e.y] none g :=
    sch_mk (j := 0) (by simp [her, he'r]) hperm none [solidC .plus e'.x e.y]
      [mkC (.waved .plus) x e.y] (by simp [mkC, Kind.isRandom])
      (List.Perm.of_eq (by simp [g, ggMain, liftCs_zero, labW])) co
  rw [hyy, solidC_self] at hS
  have hl0 : ∀ u : Atom k n, (liftA 0 u : Atom k (n + 0)) = u := liftA_zero
  -- weights
  have hlw := hS.lwN
  have hrw := hS.rwN
  simp [List.filter_cons, mkC, Kind.isLt, Kind.isRg, hf1, hf4] at hlw hrw
  -- degrees
  have hdx := hS.deg x
  have hdy := hS.deg e.y
  simp only [hl0] at hdx hdy
  simp [List.filter_cons, mkC, Kind.isSolid, atB, hf1, hf2, hf4, hf5, hyy, hf3, hf3.symm] at hdx hdy
  have hdegx : Γ.deg x = 2 := H.deg2
  obtain ⟨ix, rfl⟩ : ∃ ix, x = .inr ix := by
    rcases x with a | a
    · simp at hxR
    · exact ⟨a, rfl⟩
  have hyR : e.y.isRight = true := by
    cases sw
    · exact hyy ▸ hy'R rfl
    · exact H.eyR rfl
  obtain ⟨iy, hiy⟩ : ∃ iy, e.y = .inr iy := by
    rcases h : e.y with a | a
    · rw [h] at hyR; simp at hyR
    · exact ⟨a, rfl⟩
  have hne : ix ≠ iy := by
    intro h; apply hf3; rw [hiy, h]
  have hloc : ∀ i, i ≠ ix → i ≠ iy →
      g.deg (.inr i) = Γ.deg (.inr i) ∧ g.stdNeutralAt (.inr i) = Γ.stdNeutralAt (.inr i) := by
    intro i h1 h2
    have := hS.local_untouched (u := .inr i) (by
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · simp [atB, hf2, hiy, Ne.symm h1, Ne.symm h2]
        · simp [atB, hf5, hyy, hiy, Ne.symm h1, Ne.symm h2])
      (by
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp [atB, mkC, hl0, hiy, Ne.symm h1, Ne.symm h2])
    simpa [hl0] using this
  have hX := sum_two_eq (fun i => g.deg (.inr i) - 2) (fun i => Γ.deg (.inr i) - 2) ix iy hne
    (fun i h1 h2 => by simp only [(hloc i h1 h2).1])
  have hB := sum_two_eq (fun i => badI g (.inr i)) (fun i => badI Γ (.inr i)) ix iy hne
    (fun i h1 h2 => by simp only [badI, (hloc i h1 h2).1, (hloc i h1 h2).2])
  have hstdx : Γ.stdNeutralAt (.inr ix) = false :=
    std_false_same he he' hf1 hf4 ⟨hf2, hf3⟩ ⟨hf5, hf6⟩
  have hstdy : Γ.stdNeutralAt (.inr iy) = false := by
    rw [← hiy]
    exact std_false_same he' he hf4 hf1 ⟨hyy, by rw [hf5]; exact hf3.symm⟩ ⟨rfl, by rw [hf2]; exact hf3.symm⟩
  rw [hiy] at hdy
  have bx : badI Γ (.inr ix) = 1 := by simp [badI, hdegx, hstdx]
  have bgx : badI g (.inr ix) = 0 := by simp [badI]; omega
  have by' : badI Γ (.inr iy) = if Γ.deg (.inr iy) = 2 then 1 else 0 := by
    simp [badI, hstdy]
  have bgy : badI g (.inr iy) ≤ if g.deg (.inr iy) = 2 then 1 else 0 := by
    unfold badI; split_ifs <;> simp_all
  rw [← badN_eq, ← badN_eq] at hB
  change g.degX + _ + _ = Γ.degX + _ + _ at hX
  unfold Graph.phi
  rw [hlw, hrw]
  rw [bx, bgx, by'] at hB
  rw [hdegx] at hX
  split_ifs at hB bgy with h1 h2 h2 <;> omega

end GGPhi

/-! ## Complex conjugation of terms -/

section ConjTerm

variable {k n : ℕ}

private theorem Kind.conj_conj (κ : Kind) : κ.conj.conj = κ := by
  cases κ <;> (try cases ‹Wave›) <;> (try cases ‹Charge›) <;> rfl

private theorem Comp.conj_conj {V : Type*} (c : Comp V) : c.conj.conj = c := by
  cases c; simp [Comp.conj, Kind.conj_conj]

theorem Kind.conj_isLt (κ : Kind) : κ.conj.isLt = κ.isLt := by
  cases κ <;> (try cases ‹Wave›) <;> rfl

private theorem Kind.conj_isRg (κ : Kind) : κ.conj.isRg = κ.isRg := by
  cases κ <;> (try cases ‹Wave›) <;> rfl

private theorem Kind.conj_eq_s (κ : Kind) : (κ.conj == .waved .s) = (κ == .waved .s) := by
  cases κ <;> (try cases ‹Wave›) <;> rfl

private theorem Kind.conj_ne_xdot (κ : Kind) : (κ.conj != .xdot) = (κ != .xdot) := by
  cases κ <;> (try cases ‹Wave›) <;> rfl

private theorem Kind.conj_eq_xdot' (κ : Kind) : (κ.conj == .xdot) = (κ == .xdot) := by
  cases κ <;> (try cases ‹Wave›) <;> rfl

theorem Graph.conj_deg' {m : ℕ} (g : Graph k m) (u : Atom k m) : g.conj.deg u = g.deg u := by
  unfold Graph.deg
  rw [Graph.conj_comps, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro c _
  simp [Function.comp, Kind.conj_isSolid]

private theorem Graph.conj_ends {m : ℕ} (g : Graph k m) (u : Atom k m) :
    g.conj.ends u = (g.ends u).map fun e => (e.1, e.2.flip) := by
  unfold Graph.ends
  rw [Graph.conj_comps, List.filterMap_map, List.map_filterMap]
  congr 1
  funext c
  rcases c with ⟨κ, a, b, mi, l⟩
  simp only [Function.comp, Comp.conj]
  cases κ <;> (try cases ‹Charge›) <;> (try cases ‹Wave›) <;> simp only [Kind.conj] <;>
    (by_cases h1 : a = u <;> by_cases h2 : b = u <;> simp [h1, h2, Charge.flip])

private theorem stdM_flip (l : List (Bool × Charge)) :
    stdM (l.map fun e => (e.1, e.2.flip)) = stdM l := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp [stdM]
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> rfl

private theorem Graph.conj_std {m : ℕ} (g : Graph k m) (u : Atom k m) :
    g.conj.stdNeutralAt u = g.stdNeutralAt u := by
  rw [std_eq, std_eq, Graph.conj_ends, stdM_flip, Graph.conj_comps]
  rw [List.filter_map, List.filter_map, List.filter_map, List.filter_map]
  simp only [List.length_map, Function.comp_def, Comp.conj_kind, Kind.conj_ne_xdot,
    Kind.conj_isSolid, Kind.conj_eq_s]
  rfl

private theorem Graph.conj_phi {m : ℕ} (g : Graph k m) : g.conj.phi = g.phi := by
  have h1 : g.conj.lwN = g.lwN := by
    simp [Graph.lwN, Graph.conj_comps, List.filter_map, Function.comp_def, Kind.conj_isLt]
  have h2 : g.conj.rwN = g.rwN := by
    simp [Graph.rwN, Graph.conj_comps, List.filter_map, Function.comp_def, Kind.conj_isRg]
  have h3 : g.conj.degX = g.degX := by simp [Graph.degX, Graph.conj_deg']
  have h4 : g.conj.badN = g.badN := by simp [Graph.badN, Graph.conj_deg', Graph.conj_std]
  simp [Graph.phi, h1, h2, h3, h4]

private theorem Graph.conj_hasXdot {m : ℕ} (g : Graph k m) (u v : Atom k m) :
    g.conj.hasXdot u v = g.hasXdot u v := by
  simp [Graph.hasXdot, Graph.conj_comps, List.any_map, Function.comp_def, Kind.conj_eq_xdot']

private theorem Graph.conj_molGraph {m : ℕ} (g : Graph k m) : g.conj.molGraph = g.molGraph := by
  unfold Graph.molGraph
  congr 1
  funext u v
  apply propext
  rw [Graph.conj_comps]
  constructor
  · rintro ⟨c, hc, h1, h2⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    exact ⟨d, hd, by simpa [Kind.conj_joinsMol] using h1, h2⟩
  · rintro ⟨c, hc, h1, h2⟩
    exact ⟨c.conj, List.mem_map_of_mem hc, by simpa [Kind.conj_joinsMol] using h1, h2⟩

private theorem Graph.conj_sameMol {m : ℕ} (g : Graph k m) (u v : Atom k m) :
    g.conj.SameMol u v ↔ g.SameMol u v := by
  simp [Graph.SameMol, Graph.conj_molGraph]

private theorem labF_conj {V : Type*} (lab : Option V) (c : Comp V) :
    (labF lab c).conj = labF lab c.conj := by
  cases lab with
  | none => rfl
  | some u =>
    show (Comp.labelQ u c).conj = Comp.labelQ u c.conj
    unfold Comp.labelQ
    simp only [Comp.conj_kind, Kind.conj_isRandom]
    split_ifs <;> rfl

private theorem liftCs_conj {j : ℕ} (K : List (Comp (Atom k n))) :
    (liftCs j K).map Comp.conj = liftCs j (K.map Comp.conj) := by
  simp [liftCs, Comp.conj, Comp.map, List.map_map, Function.comp_def]

theorem Sch.conj {j : ℕ} {Γ : Graph k n} {R : List (Comp (Atom k n))}
    {N : List (Comp (Atom k (n + j)))} {lab : Option (Atom k (n + j))} {g : Graph k (n + j)}
    (hS : Sch Γ.conj j R N lab g) :
    Sch Γ j (R.map Comp.conj) (N.map Comp.conj) lab g.conj := by
  obtain ⟨hR, K, h1, h2⟩ := hS
  refine ⟨fun c hc => ?_, K.map Comp.conj, ?_, ?_⟩
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    simpa [Kind.conj_isRandom] using hR d hd
  · have : Γ.comps = Γ.conj.comps.map Comp.conj := by
      simp [Graph.conj_comps, List.map_map, Function.comp_def, Comp.conj_conj]
    rw [this, ← List.map_append]
    exact h1.map _
  · rw [Graph.conj_comps]
    refine (h2.map _).trans (List.Perm.of_eq ?_)
    rw [List.map_map, ← liftCs_conj, ← List.map_append, List.map_map]
    apply List.map_congr_left
    intro c _
    simp [Function.comp, labF_conj]

private theorem kAt_conj {V : Type*} (sw : Bool) (c : Comp V) : kAt sw c.conj = kAt sw c := by
  cases sw <;> simp [kAt, Kind.conj_isSolid]

/-- A term of `Ô` at the complex conjugate graph, conjugated back. -/
private theorem TermOKS.conj {sw : Bool} {Γ : Graph k n} {x : Atom k n} {T : Tracked k n}
    (hT : TermOKS sw Γ.conj x T) :
    TermOKS sw Γ x ⟨T.nOut, T.g.conj, T.f⟩ := by
  obtain ⟨j, R, N, lab, g, s, rfl, hS, hNo, hNK, hs, two, old, four, zero, hext, hphi, hlab,
    hatt⟩ := hT
  have hlen : ∀ (P : Comp (Atom k (n + j)) → Bool), (∀ c, P c.conj = P c) →
      ((N.map Comp.conj).filter P).length = (N.filter P).length := by
    intro P hP
    rw [List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro c _
    simp [Function.comp, hP]
  refine ⟨j, R.map Comp.conj, N.map Comp.conj, lab, g.conj, s, rfl, hS.conj, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    obtain ⟨⟨p1, p2, p3, p4, p5⟩, hl⟩ := hNo d hd
    refine ⟨⟨p1, ?_, ?_, ?_, ?_⟩, hl⟩
    · rcases p2 with ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨w, h⟩ <;> simp only [Comp.conj_kind, h]
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inr (Or.inl ⟨_, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
      · cases w <;> exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))
    · simpa [Kind.conj_isWeight] using p3
    · simpa [Kind.conj_isSolid] using p4
    · simpa [Kind.conj_isRandom] using p5
  · intro c hc hr
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [kAt_conj]
    exact hNK d hd (by simpa [Kind.conj_isRandom] using hr)
  · have e1 : ∀ L : List (Comp (Atom k (n + j))), ordL (L.map Comp.conj) = ordL L := by
      intro L; simp [ordL, List.map_map, Function.comp_def, Kind.conj_ord]
    have e2 : ∀ L : List (Comp (Atom k n)), ordL (L.map Comp.conj) = ordL L := by
      intro L; simp [ordL, List.map_map, Function.comp_def, Kind.conj_ord]
    rw [e1, e2]; exact hs
  · intro i; rw [hlen _ (fun c => by simp [Kind.conj_isSolid, atB])]; exact two i
  · rw [hlen _ (fun c => by simp [Kind.conj_isSolid, Graph.conj_hasXdot])]
    simpa [Graph.conj_hasXdot] using old
  · rw [hlen _ (fun c => by simp [Kind.conj_isSolid])]; exact four
  · intro h; rw [hlen _ (fun c => by simp [Kind.conj_isSolid])]; exact zero h
  · rw [hlen _ (fun c => by simp [Kind.conj_isSolid])]
    have : ((R.map Comp.conj).filter fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length =
        (R.filter fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length := by
      rw [List.filter_map, List.length_map]
      congr 1
      apply List.filter_congr
      intro c _
      simp [Function.comp, Kind.conj_isSolid]
    rw [this]; exact hext
  · intro hl hs0
    have := hphi hl hs0
    rw [Graph.conj_phi] at this
    rw [Graph.conj_phi]
    exact this
  · intro hl
    obtain ⟨c, hc, hr⟩ := hlab hl
    exact ⟨c.conj, List.mem_map_of_mem hc, by simpa [Kind.conj_isRandom] using hr⟩
  · intro i
    exact (Graph.conj_sameMol _ _ _).2 (hatt i)

/-- A term of `Ô` at the complex conjugate graph, conjugated back. -/
private theorem TermOK.conj {Γ : Graph k n} {x : Atom k n} {T : Tracked k n} (hT : TermOK Γ.conj x T) :
    TermOK Γ x ⟨T.nOut, T.g.conj, T.f⟩ := TermOKS.conj hT

end ConjTerm

section EdgeCopies

variable {k n N : ℕ}


private theorem wt_zero_imp {Γ : Graph k n} {x : Atom k n} (h : Γ.wt x = 0) {c : Comp (Atom k n)}
    (hc : c ∈ Γ.comps) (hk : (∃ ch, c.kind = .weight ch) ∨ (∃ ch, c.kind = .light ch)) :
    c.x ≠ x := by
  intro hcx
  unfold Graph.wt at h
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h
  have := h c hc
  rcases hk with ⟨ch, hch⟩ | ⟨ch, hch⟩ <;> simp [hch, hcx] at this

private theorem fL_untouched {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C)
    {c : Comp (Atom k n)} (hc : c ∈ eraseIdxs (oXIdx x Γ) Γ.comps) {ch : Charge}
    (hk : c.kind = .G ch) : c.x ≠ x ∧ c.y ≠ x := by
  obtain ⟨i, hi, hn⟩ := mem_eraseIdxs_iff.1 hc
  have hcm : c ∈ Γ.comps := mem_eraseIdxs_of_mem hc
  have hsl := hN.2.1 c hcm (by simp [hk, Kind.isSolid])
  constructor
  · intro hcx
    exact hn (mem_oXIdx.2 ⟨c, hi, ch, hk, Or.inl ⟨hcx, by rw [← hcx]; exact fun h => hsl h.symm⟩⟩)
  · intro hcy
    exact hn (mem_oXIdx.2 ⟨c, hi, ch, hk, Or.inr ⟨hcy, by rw [← hcy]; exact hsl⟩⟩)


private theorem deg_eq_countP (g : Graph k N) (u : Atom k N) :
    g.deg u = g.comps.countP (fun c => c.kind.isSolid && (c.x == u || c.y == u)) := by
  unfold Graph.deg
  rw [List.countP_eq_length_filter]


private theorem zipIdx_map' {α β : Type*} (f : α → β) (l : List α) (m : ℕ) :
    (l.map f).zipIdx m = (l.zipIdx m).map (fun p => (f p.1, p.2)) := by
  induction l generalizing m with
  | nil => rfl
  | cons a l ih => simp [List.zipIdx_cons, ih]

theorem edgeIdx_conj (Γ : Graph k n) (x : Atom k n) (ch : Charge) (out : Bool) :
    Γ.conj.edgeIdx x ch out = Γ.edgeIdx x ch.flip out := by
  unfold Graph.edgeIdx
  rw [Graph.conj_comps, zipIdx_map', List.filter_map, List.map_map]
  congr 1
  · apply List.filter_congr
    intro p _
    rw [Bool.eq_iff_iff]
    cases ch <;> rcases p with ⟨⟨κ, a, b, mi, l⟩, i⟩ <;>
      cases κ <;> (try cases ‹Charge›) <;> (try cases ‹Wave›) <;>
      simp [Comp.conj, Kind.conj, Charge.flip]

theorem OutCtxS.conj_of {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hN : Γ.Normal C) (hP : Γ.Plain) (hx : x.isRight = true)
    (hU : ∀ c ∈ Γ.comps, c.label = none) (hOP : Γ.edgeIdx x .minus true = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) : OutCtxS C x Γ.conj i₁ is₂ e₁.conj where
  normal := Graph.conj_Normal hN
  plain := Graph.conj_Plain hP
  right := hx
  unl := fun c' hc' => by
    obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
    simpa using hU c hc
  hOP := by rw [edgeIdx_conj]; exact hOP
  hL := by simp [Graph.conj_comps, hL]


theorem xdotsAt_of_normal {C : ℕ} {Γ : Graph k n} (hN : Γ.Normal C) (x : Atom k n)
    (is : List ℕ) (h : ∀ j ∈ is, ∃ c, Γ.comps[j]? = some c ∧ c.kind.isSolid = true ∧
      (c.x = x ∨ c.y = x)) : Γ.xdotsAt x is = true := by
  unfold Graph.xdotsAt
  rw [List.all_eq_true]
  intro j hj
  obtain ⟨c, hc, hs, hxy⟩ := h j hj
  rw [hc]
  simp only
  have hcm : c ∈ Γ.comps := List.mem_of_getElem? hc
  have hne : c.x ≠ c.y := hN.2.1 c hcm hs
  unfold Graph.hasXdot
  rw [List.any_eq_true]
  by_cases hcx : c.x = x
  · have hzx : c.y ≠ x := fun h' => hne (hcx.trans h'.symm)
    obtain ⟨c₂, hc₂, hk₂, hm₂⟩ := (hN.2.2 x c.y (Ne.symm hzx)).2 ⟨c, hcm, hs, Or.inl ⟨hcx, rfl⟩⟩
    refine ⟨c₂, hc₂, ?_⟩
    simp only [hcx, beq_self_eq_true, ite_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    refine ⟨by simpa using hk₂, ?_⟩
    rcases hm₂ with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact Or.inl ⟨a1, a2⟩
    · exact Or.inr ⟨a1, a2⟩
  · have hcy : c.y = x := hxy.resolve_left hcx
    have hzx : c.x ≠ x := hcx
    obtain ⟨c₂, hc₂, hk₂, hm₂⟩ := (hN.2.2 x c.x (Ne.symm hzx)).2 ⟨c, hcm, hs, Or.inr ⟨rfl, hcy⟩⟩
    refine ⟨c₂, hc₂, ?_⟩
    have : (c.x == x) = false := by simpa using hcx
    simp only [this, Bool.false_eq_true, ite_false, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    refine ⟨by simpa using hk₂, ?_⟩
    rcases hm₂ with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact Or.inl ⟨a1, a2⟩
    · exact Or.inr ⟨a1, a2⟩

private theorem length_filterMap_of_some {α β : Type*} (f : α → Option β) (l : List α)
    (h : ∀ i ∈ l, ∃ c, f i = some c) : (l.filterMap f).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨c, hc⟩ := h a (List.mem_cons_self ..)
    simp [hc, ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]

theorem deg_eq_sum {C : ℕ} {Γ : Graph k n} (hN : Γ.Normal C) (x : Atom k n) :
    Γ.deg x = (Γ.edgeIdx x .plus true).length + (Γ.edgeIdx x .minus true).length +
      (Γ.edgeIdx x .plus false).length + (Γ.edgeIdx x .minus false).length := by
  have hperm := eraseIdxs_pick_perm (oXIdx x Γ) Γ.comps
  have hnd := oXIdx_nodup x Γ
  have hpp := pickIdxs_perm (oXIdx x Γ) hnd Γ.comps
  rw [deg_eq_countP, ← hperm.countP_eq, List.countP_append]
  have h0 : (eraseIdxs (oXIdx x Γ) Γ.comps).countP
      (fun c => c.kind.isSolid && (c.x == x || c.y == x)) = 0 := by
    rw [List.countP_eq_zero]
    intro c hc hcon
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcon
    obtain ⟨hs, hxy⟩ := hcon
    obtain ⟨ch, hch⟩ : ∃ ch, c.kind = .G ch := by
      cases hk : c.kind <;> simp_all [Kind.isSolid]
    obtain ⟨a, b⟩ := fL_untouched hN hc hch
    rcases hxy with h | h
    · exact a h
    · exact b h
  have hlen : (pickIdxs (oXIdx x Γ) Γ.comps).length = (oXIdx x Γ).length := by
    rw [hpp.length_eq]
    apply length_filterMap_of_some
    intro i hi
    obtain ⟨c, hc, -⟩ := mem_oXIdx.1 hi
    exact ⟨c, hc⟩
  have h1 : (pickIdxs (oXIdx x Γ) Γ.comps).countP
      (fun c => c.kind.isSolid && (c.x == x || c.y == x)) = (oXIdx x Γ).length := by
    rw [← hlen, List.countP_eq_length]
    intro c hc
    obtain ⟨i, hi, hic⟩ := List.mem_filterMap.1 (hpp.subset hc)
    obtain ⟨c', hc', ch, hk, hxy⟩ := mem_oXIdx.1 hi
    have : c = c' := by
      rw [hc'] at hic
      exact (Option.some.inj hic).symm
    rw [this]
    rcases hxy with ⟨h1', -⟩ | ⟨h1', -⟩ <;> simp [hk, Kind.isSolid, h1']
  rw [h0, h1]
  simp only [oXIdx, List.length_append]
  omega


theorem all_isPlainB {Γ : Graph k n} (hlf : Γ.LabelFree) (hP : Γ.Plain) :
    Γ.comps.all Comp.isPlainB = true := by
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨h1, h2, h3, -⟩ := hP c hc
  have hl := hlf c hc
  unfold Comp.isPlainB
  rcases hk : c.kind with ch | ch | ch | ch | ⟨ch, d⟩ | w | o | ⟨a, b⟩ | _ | ⟨a, b, c'⟩ | _ | _ <;>
    simp_all


private theorem idx_of_mem {α : Type*} {l : List α} {a : α} (h : a ∈ l) : ∃ i : ℕ, l[i]? = some a :=
  List.mem_iff_getElem?.1 h

theorem gg_input {C : ℕ} {Γ : Graph k n} {x y y' : Atom k n} (hN : Γ.Normal C)
    (h : Γ.GGInputAt x y y') :
    ∃ ch : Charge, ∃ i j : ℕ, ∃ e e' : Comp (Atom k n),
      Γ.edgeIdx x ch true = [i] ∧ Γ.edgeIdx x ch false = [j] ∧
      Γ.edgeIdx x ch.flip true = [] ∧ Γ.edgeIdx x ch.flip false = [] ∧
      Γ.comps[i]? = some e ∧ Γ.comps[j]? = some e' := by
  obtain ⟨hdeg, ch, ⟨c, hc, hk, hxc, hyc⟩, ⟨c', hc', hk', hxc', hyc'⟩⟩ := h
  have hsum : ∀ ch : Charge, Γ.deg x = (Γ.edgeIdx x ch true).length +
      (Γ.edgeIdx x ch.flip true).length + (Γ.edgeIdx x ch false).length +
      (Γ.edgeIdx x ch.flip false).length := by
    intro ch
    have := deg_eq_sum hN x
    cases ch <;> simp only [Charge.flip] <;> omega
  obtain ⟨ip, hip⟩ := idx_of_mem hc
  obtain ⟨jp, hjp⟩ := idx_of_mem hc'
  have hs1 := hN.2.1 c hc (by simp [hk, Kind.isSolid])
  have hs2 := hN.2.1 c' hc' (by simp [hk', Kind.isSolid])
  have hmp : ip ∈ Γ.edgeIdx x ch true :=
    mem_edgeIdx.2 ⟨c, hip, hk, hxc, fun h => hs1 (hxc.trans h.symm)⟩
  have hmm : jp ∈ Γ.edgeIdx x ch false :=
    mem_edgeIdx.2 ⟨c', hjp, hk', hyc', fun h => hs2 (h.trans hyc'.symm)⟩
  have p1 := List.length_pos_of_mem hmp
  have p2 := List.length_pos_of_mem hmm
  have hs := hsum ch
  have l1 : (Γ.edgeIdx x ch true).length = 1 := by omega
  have l2 : (Γ.edgeIdx x ch false).length = 1 := by omega
  have l3 : (Γ.edgeIdx x ch.flip true).length = 0 := by omega
  have l4 : (Γ.edgeIdx x ch.flip false).length = 0 := by omega
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 l1
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 l2
  have hia : ip = a := by rw [ha] at hmp; simpa using hmp
  have hib : jp = b := by rw [hb] at hmm; simpa using hmm
  exact ⟨ch, a, b, c, c', ha, hb, List.length_eq_zero_iff.1 l3, List.length_eq_zero_iff.1 l4,
    by rw [← hia]; exact hip, by rw [← hib]; exact hjp⟩

theorem ggPos_eq {x : Atom k n} {Γ : Graph k n} {i j : ℕ} {e e' : Comp (Atom k n)}
    (hdeg : Γ.deg x = 2) (hPO : Γ.edgeIdx x .plus true = [i])
    (hPI : Γ.edgeIdx x .plus false = [j]) (hi : Γ.comps[i]? = some e)
    (hj : Γ.comps[j]? = some e') (hX : Γ.xdotsAt x [i, j] = true) :
    ggPos x Γ = some (ggOut x Γ i j e e') := by
  unfold ggPos
  rw [ite_eq_right (by simp [hdeg]), hPO, hPI]
  simp only [hi, hj]
  rw [ite_eq_right (by simp [hX])]
  rfl


end EdgeCopies

/-! ## The number of graphs produced by one step -/

section Lengths

variable {k n : ℕ}

private theorem len_dTerms {V : Type*} [DecidableEq V] (p q : V) (cs : List (Comp V)) :
    (dTerms p q cs).length ≤ cs.length := by
  unfold dTerms
  exact (List.length_filterMap_le _ _).trans (by simp)

private theorem len_edgeIdx (Γ : Graph k n) (x : Atom k n) (ch : Charge) (out : Bool) :
    (Γ.edgeIdx x ch out).length ≤ Γ.comps.length := by
  unfold Graph.edgeIdx
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

private theorem len_eraseIdxs {α : Type*} (is : List ℕ) (l : List α) :
    (eraseIdxs is l).length ≤ l.length := by
  unfold eraseIdxs
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

private theorem len_ite_single {α : Type*} (p : Prop) [Decidable p] (a : α) :
    (if p then ([] : List α) else [a]).length ≤ 1 := by
  split_ifs <;> simp

private theorem len_ggOut (x : Atom k n) (Γ : Graph k n) (i j : ℕ) (e e' : Comp (Atom k n)) :
    (ggOut x Γ i j e e').length ≤ 4 * Γ.comps.length + 12 := by
  have h1 : (ggD1 x Γ i j e e').length ≤ Γ.comps.length := by
    unfold ggD1
    rw [List.length_map]
    refine (len_dTerms _ _ _).trans ?_
    simp only [liftCs, List.length_map, ggF]
    exact len_eraseIdxs _ _
  have h2 : (ggD2 Γ i j e e').length ≤ Γ.comps.length := by
    unfold ggD2
    rw [List.length_map]
    refine (len_dTerms _ _ _).trans ?_
    simp only [liftCs, List.length_map, ggF]
    exact len_eraseIdxs _ _
  unfold ggOut
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  omega

end Lengths

/-! ## The step of the `GG` expansion -/

section GGStep

variable {k n : ℕ}

private theorem GGHyp.allTerms {sw : Bool} {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i j : ℕ}
    {e e' : Comp (Atom k n)}
    (H : GGHyp sw C x Γ i j e e') : ∀ T ∈ ggOut x Γ i j e e', TermOKS sw Γ x T := by
  intro T hT
  have hx := H.ctx.right
  unfold ggOut at hT
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  rcases hT with (((((rfl | rfl | rfl | rfl | rfl) | ⟨d, hd, rfl⟩) | ⟨d, hd, rfl⟩) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl)) | ⟨d, hd, rfl⟩) | ⟨d, hd, rfl⟩
  · exact H.termMain none (Or.inl rfl) _ (fun _ hyy => H.phi_main hyy _)
  · exact H.term2
  · exact H.term3 _
  · exact H.term4 _
  · exact H.term5 _
  · exact H.termD1 hd none _
  · exact H.termD2 hd none _
  · exact termQx hx ⟨e, H.ctx.emem, by simp [H.ctx.espec.1, Kind.isRandom]⟩ _
  · exact H.termQ2 _
  · exact H.termMain (some e.y) (Or.inr rfl) _ (fun h => absurd h (by simp))
  · exact termQxl hx _
  · exact H.termQ5 _
  · exact H.termQ6 _
  · exact H.termQ7 _
  · exact H.termD1 hd (some (liftA 1 x)) _
  · exact H.termD2 hd (some (newA 0)) _

theorem Graph.conj_randomFirstInt {Γ : Graph k n} (h : Γ.RandomFirstInt) : Γ.conj.RandomFirstInt := by
  intro c hc hr
  obtain ⟨d, hd, rfl⟩ := Graph.mem_conj_comps.1 hc
  exact h d hd (by simpa [Kind.conj_isRandom] using hr)

theorem Graph.conj_labelFree' {Γ : Graph k n} (h : Γ.LabelFree) : Γ.conj.LabelFree := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := Graph.mem_conj_comps.1 hc
  simpa using h d hd

/-- Every output of a bind of `O_dot` over terms with `TermOK` satisfies `StepOut`. -/
private theorem bind_step {C : ℕ} {x : Atom k n} {Γ : Graph k n} {E : TExpansion k n}
    (hE : ∀ T ∈ E, TermOK Γ x T) (hN : Γ.Normal C) (hP : Γ.Plain) (hL : Γ.LabelFree)
    (hK : Γ.RandomFirstInt) (hX : Γ.XdotApart) :
    ∀ t ∈ E.bind (fun _ g => oDotT g), StepOut Γ t := by
  intro t ht
  simp only [TExpansion.bind, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨T, hT, s, hs, rfl⟩ := ht
  exact (hE T hT).step hN hP hL hK hX hs

/-- The `GG` expansion at `x` is `O_dot` applied to at most `4 · #components + 12` terms of a local
operation. -/
theorem oGGT_rep {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C) (hP : Γ.Plain)
    (hL : Γ.LabelFree) (hK : Γ.RandomFirstInt) (hx : x.isRight = true)
    (hwt : Γ.wt x = 0) {y y' : Atom k n} (hin : Γ.GGInputAt x y y') :
    ∃ E : TExpansion k n, oGGT x Γ = E.bind (fun _ g => oDotT g) ∧ (∀ T ∈ E, TermOK Γ x T) ∧
      E.length ≤ 4 * Γ.comps.length + 12 := by
  obtain ⟨ch, i, j, e, e', hO, hI, hO', hI', hi, hj⟩ := gg_input hN hin
  have hpl : (!Γ.comps.all Comp.isPlainB) = false := by simp [all_isPlainB hL hP]
  have hdeg := hin.1
  cases ch
  · simp only [Charge.flip] at hO' hI'
    have Ctx : GGCtxS C x Γ i j e e' := ⟨hN, hP, hx, hL, hO, hI, hO', hI', hi, hj⟩
    have hX' : Γ.xdotsAt x [i, j] = true := by
      refine xdotsAt_of_normal hN x [i, j] fun m hm => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact ⟨e, hi, by simp [Ctx.espec.1, Kind.isSolid], Or.inl Ctx.espec.2.1⟩
      · exact ⟨e', hj, by simp [Ctx.e'spec.1, Kind.isSolid], Or.inr Ctx.e'spec.2.1⟩
    have hE : oGGT x Γ = (ggOut x Γ i j e e').bind (fun _ g => oDotT g) := by
      unfold oGGT
      rw [ite_eq_right (by simp [hpl]), ggPos_eq hdeg hO hI hi hj hX']
    exact ⟨_, hE, GGHyp.allTerms (sw := false) ⟨Ctx, hK, hwt, hdeg⟩, len_ggOut _ _ _ _ _ _⟩
  · simp only [Charge.flip] at hO' hI'
    have hi' : Γ.conj.comps[i]? = some e.conj := by simp [Graph.conj_comps, hi]
    have hj' : Γ.conj.comps[j]? = some e'.conj := by simp [Graph.conj_comps, hj]
    have hO2 : Γ.conj.edgeIdx x .plus true = [i] := by rw [edgeIdx_conj]; exact hO
    have hI2 : Γ.conj.edgeIdx x .plus false = [j] := by rw [edgeIdx_conj]; exact hI
    have hM1 : Γ.conj.edgeIdx x .minus true = [] := by rw [edgeIdx_conj]; exact hO'
    have hM2 : Γ.conj.edgeIdx x .minus false = [] := by rw [edgeIdx_conj]; exact hI'
    have Ctx : GGCtxS C x Γ.conj i j e.conj e'.conj :=
      ⟨Graph.conj_Normal hN, Graph.conj_Plain hP, hx, Graph.conj_labelFree' hL, hO2, hI2, hM1, hM2,
        hi', hj'⟩
    have hX' : Γ.conj.xdotsAt x [i, j] = true := by
      refine xdotsAt_of_normal (Graph.conj_Normal hN) x [i, j] fun m hm => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact ⟨e.conj, hi', by rw [Ctx.espec.1]; rfl, Or.inl Ctx.espec.2.1⟩
      · exact ⟨e'.conj, hj', by rw [Ctx.e'spec.1]; rfl, Or.inr Ctx.e'spec.2.1⟩
    have hdeg' : Γ.conj.deg x = 2 := by rw [Graph.conj_deg']; exact hdeg
    have hnone : ggPos x Γ = none := by
      unfold ggPos
      rw [ite_eq_right (by simp [hdeg])]
      have : Γ.edgeIdx x .plus true = [] := hO'
      rw [this]
    have hE : oGGT x Γ = (ggOut x Γ.conj i j e.conj e'.conj).conj.bind (fun _ g => oDotT g) := by
      unfold oGGT
      rw [ite_eq_right (by simp [hpl]), hnone]
      simp only
      rw [ggPos_eq hdeg' hO2 hI2 hi' hj' hX']
    have H : GGHyp false C x Γ.conj i j e.conj e'.conj :=
      ⟨Ctx, Graph.conj_randomFirstInt hK, by rw [Graph.conj_wt]; exact hwt, hdeg'⟩
    refine ⟨_, hE, fun T hT => ?_, ?_⟩
    · obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
      exact (H.allTerms T₀ hT₀).conj
    · unfold TExpansion.conj
      rw [List.length_map]
      exact (len_ggOut _ _ _ _ _ _).trans (by simp [Graph.conj_comps])

/-- The step of the `GG` expansion at `x`: every output has the clauses `StepOut`. -/
theorem oGGT_step {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C) (hP : Γ.Plain)
    (hL : Γ.LabelFree) (hK : Γ.RandomFirstInt) (hX : Γ.XdotApart) (hx : x.isRight = true)
    (hwt : Γ.wt x = 0) {y y' : Atom k n} (hin : Γ.GGInputAt x y y') :
    ∀ t ∈ oGGT x Γ, StepOut Γ t := by
  obtain ⟨E, hE, hT, -⟩ := oGGT_rep hN hP hL hK hx hwt hin
  rw [hE]
  exact bind_step hT hN hP hL hK hX

end GGStep

/-! ## Reversing the solid edges of a term -/

section SwapTerm

variable {k n : ℕ}

theorem Comp.swapSolid_kind' {V : Type*} (c : Comp V) : c.swapSolid.kind = c.kind := by
  unfold Comp.swapSolid; split <;> rfl

private theorem Comp.swapSolid_label' {V : Type*} (c : Comp V) : c.swapSolid.label = c.label := by
  unfold Comp.swapSolid; split <;> rfl

private theorem Comp.swapSolid_of_ns {V : Type*} {c : Comp V} (h : c.kind.isSolid = false) :
    c.swapSolid = c := by
  simp [Comp.swapSolid, h]

private theorem Comp.swapSolid_swapSolid' {V : Type*} (c : Comp V) : c.swapSolid.swapSolid = c := by
  rcases c with ⟨κ, a, b, m, l⟩
  by_cases h : κ.isSolid = true <;> simp [Comp.swapSolid, h]

theorem Graph.swapSolid_comps' {m : ℕ} (g : Graph k m) :
    g.swapSolid.comps = g.comps.map Comp.swapSolid := rfl

private theorem labF_swap {V : Type*} (lab : Option V) (c : Comp V) :
    (labF lab c).swapSolid = labF lab c.swapSolid := by
  rcases c with ⟨κ, a, b, m, l⟩
  cases lab with
  | none => rfl
  | some u =>
    by_cases h : κ.isSolid = true <;> by_cases h' : κ.isRandom = true <;>
      simp [labF, Comp.labelQ, Comp.swapSolid, h, h']

private theorem map_swapSolid {V W : Type*} (f : V → W) (c : Comp V) :
    (c.map f).swapSolid = c.swapSolid.map f := by
  rcases c with ⟨κ, a, b, m, l⟩
  by_cases h : κ.isSolid = true <;> simp [Comp.map, Comp.swapSolid, h]

private theorem liftCs_swap {j : ℕ} (K : List (Comp (Atom k n))) :
    (liftCs j K).map Comp.swapSolid = liftCs j (K.map Comp.swapSolid) := by
  simp [liftCs, List.map_map, Function.comp_def, map_swapSolid]

private theorem Sch.swap {j : ℕ} {Γ : Graph k n} {R : List (Comp (Atom k n))}
    {N : List (Comp (Atom k (n + j)))} {lab : Option (Atom k (n + j))} {g : Graph k (n + j)}
    (hS : Sch Γ.swapSolid j R N lab g) :
    Sch Γ j (R.map Comp.swapSolid) (N.map Comp.swapSolid) lab g.swapSolid := by
  obtain ⟨hR, K, h1, h2⟩ := hS
  refine ⟨fun c hc => ?_, K.map Comp.swapSolid, ?_, ?_⟩
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [Comp.swapSolid_kind']
    exact hR d hd
  · have : Γ.comps = Γ.swapSolid.comps.map Comp.swapSolid := by
      simp [Graph.swapSolid_comps', List.map_map, Function.comp_def, Comp.swapSolid_swapSolid']
    rw [this, ← List.map_append]
    exact h1.map _
  · rw [Graph.swapSolid_comps']
    refine (h2.map _).trans (List.Perm.of_eq ?_)
    rw [List.map_map, ← liftCs_swap, ← List.map_append, List.map_map]
    apply List.map_congr_left
    intro c _
    simp [Function.comp, labF_swap]

private theorem kAt_swap {V : Type*} (c : Comp V) : kAt false c.swapSolid = kAt true c := by
  rcases c with ⟨κ, a, b, m, l⟩
  by_cases h : κ.isSolid = true <;> simp [kAt, Comp.swapSolid, h]

private theorem NewOK.swap {V : Type*} {c : Comp V} (h : NewOK c) : NewOK c.swapSolid := by
  rcases c with ⟨κ, a, b, m, l⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  by_cases hs : κ.isSolid = true
  · simp only [Comp.swapSolid, hs, ite_true]
    exact ⟨h1, h2, fun hw => (h3 hw).symm, fun hs' he => h4 hs' he.symm, h5⟩
  · simp only [Comp.swapSolid, hs, Bool.false_eq_true, ite_false]
    exact ⟨h1, h2, h3, h4, h5⟩

private theorem atB_swap {m : ℕ} (u : Atom k m) (c : Comp (Atom k m)) :
    atB u c.swapSolid = atB u c := by
  rcases c with ⟨κ, a, b, mi, l⟩
  by_cases h : κ.isSolid = true <;> simp [atB, Comp.swapSolid, h, Bool.or_comm]

private theorem Graph.swapSolid_hasXdot {m : ℕ} (g : Graph k m) (u v : Atom k m) :
    g.swapSolid.hasXdot u v = g.hasXdot u v := by
  simp only [Graph.hasXdot, Graph.swapSolid_comps', List.any_map]
  congr 1
  funext c
  rcases c with ⟨κ, a, b, mi, l⟩
  by_cases h : κ.isSolid = true
  · have : (κ == Kind.xdot) = false := by
      cases κ <;> simp_all [Kind.isSolid]
    simp [Comp.swapSolid, h, this]
  · simp [Comp.swapSolid, h]

private theorem Graph.swapSolid_ends {m : ℕ} (g : Graph k m) (u : Atom k m) :
    g.swapSolid.ends u = (g.ends u).map fun e => (!e.1, e.2) := by
  unfold Graph.ends
  rw [Graph.swapSolid_comps', List.filterMap_map, List.map_filterMap]
  congr 1
  funext c
  rcases c with ⟨κ, a, b, mi, l⟩
  simp only [Function.comp, Comp.swapSolid]
  cases κ <;> (try cases ‹Charge›) <;> (try cases ‹Wave›) <;> simp only [Kind.isSolid] <;>
    (by_cases h1 : a = u <;> by_cases h2 : b = u <;> simp [h1, h2])

private theorem stdM_flip1 (l : List (Bool × Charge)) :
    stdM (l.map fun e => (!e.1, e.2)) = stdM l := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp [stdM]
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> rfl

private theorem Graph.swapSolid_std {m : ℕ} (g : Graph k m) (u : Atom k m) :
    g.swapSolid.stdNeutralAt u = g.stdNeutralAt u := by
  rw [std_eq, std_eq, Graph.swapSolid_ends, stdM_flip1, Graph.swapSolid_comps']
  rw [List.filter_map, List.filter_map, List.filter_map, List.filter_map]
  simp only [List.length_map, Function.comp_def, Comp.swapSolid_kind', atB_swap]

private theorem Graph.swapSolid_deg' {m : ℕ} (g : Graph k m) (u : Atom k m) :
    g.swapSolid.deg u = g.deg u := (swapSolid_basic k m g).2.2.2.2.2.1 u

private theorem Graph.swapSolid_phi {m : ℕ} (g : Graph k m) : g.swapSolid.phi = g.phi := by
  have h1 : g.swapSolid.lwN = g.lwN := by
    simp [Graph.lwN, Graph.swapSolid_comps', List.filter_map, Function.comp_def,
      Comp.swapSolid_kind']
  have h2 : g.swapSolid.rwN = g.rwN := by
    simp [Graph.rwN, Graph.swapSolid_comps', List.filter_map, Function.comp_def,
      Comp.swapSolid_kind']
  have h3 : g.swapSolid.degX = g.degX := by simp [Graph.degX, Graph.swapSolid_deg']
  have h4 : g.swapSolid.badN = g.badN := by
    simp [Graph.badN, Graph.swapSolid_deg', Graph.swapSolid_std]
  simp [Graph.phi, h1, h2, h3, h4]

/-- A term of `Ô` at the graph with every solid edge reversed, reversed back. -/
private theorem TermOKS.swap {Γ : Graph k n} {x : Atom k n} {T : Tracked k n}
    (hT : TermOKS true Γ.swapSolid x T) :
    TermOK Γ x ⟨T.nOut, T.g.swapSolid, T.f⟩ := by
  obtain ⟨j, R, N, lab, g, s, rfl, hS, hNo, hNK, hs, two, old, four, zero, hext, hphi, hlab,
    hatt⟩ := hT
  have hlen : ∀ {m : ℕ} (L : List (Comp (Atom k m))) (P : Comp (Atom k m) → Bool),
      (∀ c, P c.swapSolid = P c) → ((L.map Comp.swapSolid).filter P).length = (L.filter P).length := by
    intro m L P hP
    rw [List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro c _
    simp [Function.comp, hP]
  have hsx : ∀ {m : ℕ} (c : Comp (Atom k m)), c.kind.isSolid = true →
      c.swapSolid = { c with x := c.y, y := c.x } := by
    intro m c h; simp [Comp.swapSolid, h]
  refine ⟨j, R.map Comp.swapSolid, N.map Comp.swapSolid, lab, g.swapSolid, s, rfl, hS.swap, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    exact ⟨(hNo d hd).1.swap, by rw [Comp.swapSolid_label']; exact (hNo d hd).2⟩
  · intro c hc hr
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [kAt_swap]
    exact hNK d hd (by rwa [Comp.swapSolid_kind'] at hr)
  · have e1 : ∀ {m : ℕ} (L : List (Comp (Atom k m))), ordL (L.map Comp.swapSolid) = ordL L := by
      intro m L; simp [ordL, List.map_map, Function.comp_def, Comp.swapSolid_kind']
    rw [e1, e1]; exact hs
  · intro i
    rw [hlen _ _ (fun c => by rw [Comp.swapSolid_kind', atB_swap])]
    exact two i
  · rw [hlen _ _ (fun c => by
      by_cases h : c.kind.isSolid = true
      · rw [hsx c h]
        simp only [Graph.swapSolid_hasXdot, hasXdot_comm g c.y c.x]
        cases isNewA n c.x <;> cases isNewA n c.y <;> simp
      · rw [Comp.swapSolid_of_ns (by simpa using h)])]
    simpa [Graph.swapSolid_hasXdot] using old
  · rw [hlen _ _ (fun c => by rw [Comp.swapSolid_kind'])]; exact four
  · intro h; rw [hlen _ _ (fun c => by rw [Comp.swapSolid_kind'])]; exact zero h
  · have hP : ∀ {m : ℕ} (c : Comp (Atom k m)),
        (c.swapSolid.kind.isSolid && (c.swapSolid.x.isLeft || c.swapSolid.y.isLeft)) =
          (c.kind.isSolid && (c.x.isLeft || c.y.isLeft)) := by
      intro m c
      by_cases h : c.kind.isSolid = true
      · rw [hsx c h]; simp [Bool.or_comm]
      · rw [Comp.swapSolid_of_ns (by simpa using h)]
    rw [hlen _ _ (fun c => hP c), hlen _ _ (fun c => hP c)]
    exact hext
  · intro hl hs0
    have := hphi hl hs0
    rw [Graph.swapSolid_phi] at this ⊢
    exact this
  · intro hl
    obtain ⟨c, hc, hr⟩ := hlab hl
    exact ⟨c.swapSolid, List.mem_map_of_mem hc, by rw [Comp.swapSolid_kind']; exact hr⟩
  · intro i
    exact ((swapSolid_basic k (n + j) g).2.2.2.2.1 _ _).2 (hatt i)

end SwapTerm

/-! ## The step of the transposed `GG` expansion -/

section GGTStep

variable {k n : ℕ}

private theorem swap_rel_imp {m : ℕ} (g : Graph k m) (P : Kind → Prop) {u v : Atom k m}
    (h : ∃ c ∈ g.swapSolid.comps, P c.kind ∧ c.x = u ∧ c.y = v) :
    (∃ c ∈ g.comps, P c.kind ∧ c.x = u ∧ c.y = v) ∨
      (∃ c ∈ g.comps, P c.kind ∧ c.x = v ∧ c.y = u) := by
  obtain ⟨c, hc, hP, hx, hy⟩ := h
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  rw [Comp.swapSolid_kind'] at hP
  by_cases hs : d.kind.isSolid = true
  · simp only [Comp.swapSolid, hs, ite_true] at hx hy
    exact Or.inr ⟨d, hd, hP, hy, hx⟩
  · rw [Comp.swapSolid_of_ns (by simpa using hs)] at hx hy
    exact Or.inl ⟨d, hd, hP, hx, hy⟩

private theorem fromRel_swapSolid {m : ℕ} (g : Graph k m) (P : Kind → Prop) :
    SimpleGraph.fromRel (fun u v => ∃ c ∈ g.swapSolid.comps, P c.kind ∧ c.x = u ∧ c.y = v) =
      SimpleGraph.fromRel (fun u v => ∃ c ∈ g.comps, P c.kind ∧ c.x = u ∧ c.y = v) := by
  have key : ∀ g' : Graph k m, ∀ u v,
      (SimpleGraph.fromRel (fun u v => ∃ c ∈ g'.swapSolid.comps, P c.kind ∧ c.x = u ∧ c.y = v)).Adj
        u v →
      (SimpleGraph.fromRel (fun u v => ∃ c ∈ g'.comps, P c.kind ∧ c.x = u ∧ c.y = v)).Adj u v := by
    intro g' u v h
    rw [SimpleGraph.fromRel_adj] at h ⊢
    refine ⟨h.1, ?_⟩
    rcases h.2 with h2 | h2
    · rcases swap_rel_imp g' P h2 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr h3
    · rcases swap_rel_imp g' P h2 with h3 | h3
      · exact Or.inr h3
      · exact Or.inl h3
  ext u v
  constructor
  · exact key g u v
  · intro h
    have := key g.swapSolid u v
    rw [(swapSolid_basic k m g).1] at this
    exact this h

theorem Graph.swapSolid_Normal {m C : ℕ} {g : Graph k m} (h : g.Normal C) : g.swapSolid.Normal C := by
  obtain ⟨⟨hsz, hcon, hint, hnoint⟩, hs, hx⟩ := h
  have hE : g.swapSolid.edgeGraph = g.edgeGraph := by
    have := fromRel_swapSolid g (fun _ => True)
    simpa [Graph.edgeGraph] using this
  have hW : g.swapSolid.wavedThetaGraph = g.wavedThetaGraph := by
    have := fromRel_swapSolid g
      (fun κ => κ.joinsMol = true ∧ κ ≠ .dot ∨ κ.isDiffusive = true)
    simpa [Graph.wavedThetaGraph] using this
  refine ⟨⟨by simpa [Graph.swapSolid_comps'] using hsz, by rw [hE]; exact hcon,
    fun a b => by rw [hW]; exact hint a b, ?_⟩, ?_, ?_⟩
  · intro c hc hk
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [Comp.swapSolid_kind'] at hk
    rw [Comp.swapSolid_of_ns (by rw [hk]; rfl)]
    exact hnoint d hd hk
  · intro c hc hk
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [Comp.swapSolid_kind'] at hk
    simp only [Comp.swapSolid, hk, ite_true]
    exact fun h' => hs d hd hk h'.symm
  · intro u v huv
    have key : ∀ (Q : Kind → Prop),
        (∃ c ∈ g.swapSolid.comps, Q c.kind ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) ↔
          (∃ c ∈ g.comps, Q c.kind ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) := by
      intro Q
      constructor
      · rintro ⟨c, hc, hQ, hxy⟩
        obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
        rw [Comp.swapSolid_kind'] at hQ
        refine ⟨d, hd, hQ, ?_⟩
        by_cases hs' : d.kind.isSolid = true
        · simp only [Comp.swapSolid, hs', ite_true] at hxy
          tauto
        · rw [Comp.swapSolid_of_ns (by simpa using hs')] at hxy
          exact hxy
      · rintro ⟨d, hd, hQ, hxy⟩
        refine ⟨d.swapSolid, List.mem_map_of_mem hd, by rw [Comp.swapSolid_kind']; exact hQ, ?_⟩
        by_cases hs' : d.kind.isSolid = true
        · simp only [Comp.swapSolid, hs', ite_true]
          tauto
        · rw [Comp.swapSolid_of_ns (by simpa using hs')]
          exact hxy
    rw [key (fun κ => κ = .xdot), key (fun κ => κ.isSolid = true)]
    exact hx u v huv

theorem swap_ggInput {Γ : Graph k n} {x y y' : Atom k n} (h : Γ.GGInputAt x y y') :
    Γ.swapSolid.GGInputAt x y' y := by
  obtain ⟨hd, ch, ⟨c, hc, hk, h1, h2⟩, ⟨c', hc', hk', h1', h2'⟩⟩ := h
  have hs : ∀ d : Comp (Atom k n), d.kind = .G ch → d.swapSolid = { d with x := d.y, y := d.x } :=
    fun d hk => by simp [Comp.swapSolid, hk, Kind.isSolid]
  refine ⟨by rw [Graph.swapSolid_deg']; exact hd, ch, ⟨c'.swapSolid, List.mem_map_of_mem hc',
    by rw [Comp.swapSolid_kind']; exact hk', ?_⟩, ⟨c.swapSolid, List.mem_map_of_mem hc,
    by rw [Comp.swapSolid_kind']; exact hk, ?_⟩⟩
  · rw [hs c' hk']; exact ⟨h2', h1'⟩
  · rw [hs c hk]; exact ⟨h2, h1⟩

/-- The transposed `GG` expansion at `x` is `O_dot` applied to at most `4 · #components + 12` terms
of a local operation. -/
theorem oGGTT_rep {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C) (hP : Γ.Plain)
    (hL : Γ.LabelFree) (hK : Γ.RandomFirstInt) (hx : x.isRight = true)
    (hwt : Γ.wt x = 0) {y y' : Atom k n} (hin : Γ.GGInputAt x y y') :
    ∃ E : TExpansion k n, oGGTT x Γ = E.bind (fun _ g => oDotT g) ∧ (∀ T ∈ E, TermOK Γ x T) ∧
      E.length ≤ 4 * Γ.comps.length + 12 := by
  have hB := swapSolid_basic k n Γ
  have hN' : Γ.swapSolid.Normal C := Graph.swapSolid_Normal hN
  have hP' : Γ.swapSolid.Plain := hB.2.2.2.1.2 hP
  have hL' : Γ.swapSolid.LabelFree := hB.2.2.1.2 hL
  have hwt' : Γ.swapSolid.wt x = 0 := by rw [hB.2.2.2.2.2.2.1]; exact hwt
  have hin' : Γ.swapSolid.GGInputAt x y' y := swap_ggInput hin
  have hK' : ∀ c ∈ Γ.swapSolid.comps, c.kind.isRandom = true → (kAt true c).isRight = true := by
    intro c hc hr
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [← kAt_swap, Comp.swapSolid_swapSolid']
    exact hK d hd (by rwa [Comp.swapSolid_kind'] at hr)
  obtain ⟨ch, i, j, e, e', hO, hI, hO', hI', hi, hj⟩ := gg_input hN' hin'
  have hpl : (!Γ.comps.all Comp.isPlainB) = false := by simp [all_isPlainB hL hP]
  have hdeg := hin'.1
  have hswap : ∀ E : TExpansion k n, (∀ T ∈ E, TermOKS true Γ.swapSolid x T) →
      ∀ T ∈ E.swapSolid, TermOK Γ x T := by
    intro E hE T hT
    obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
    exact (hE T₀ hT₀).swap
  have hsl : ∀ E : TExpansion k n, E.swapSolid.length = E.length := fun E => List.length_map _
  cases ch
  · simp only [Charge.flip] at hO' hI'
    have Ctx : GGCtxS C x Γ.swapSolid i j e e' := ⟨hN', hP', hx, hL', hO, hI, hO', hI', hi, hj⟩
    have hX' : Γ.swapSolid.xdotsAt x [i, j] = true := by
      refine xdotsAt_of_normal hN' x [i, j] fun m hm => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact ⟨e, hi, by simp [Ctx.espec.1, Kind.isSolid], Or.inl Ctx.espec.2.1⟩
      · exact ⟨e', hj, by simp [Ctx.e'spec.1, Kind.isSolid], Or.inr Ctx.e'spec.2.1⟩
    have hE : oGGTT x Γ = (ggOut x Γ.swapSolid i j e e').swapSolid.bind (fun _ g => oDotT g) := by
      unfold oGGTT
      rw [ite_eq_right (by simp [hpl]), ggPos_eq hdeg hO hI hi hj hX']
    refine ⟨_, hE, hswap _ (GGHyp.allTerms (sw := true) ⟨Ctx, hK', hwt', hdeg⟩), ?_⟩
    rw [hsl]
    exact (len_ggOut _ _ _ _ _ _).trans (by simp [Graph.swapSolid_comps'])
  · simp only [Charge.flip] at hO' hI'
    have hi' : Γ.swapSolid.conj.comps[i]? = some e.conj := by simp [Graph.conj_comps, hi]
    have hj' : Γ.swapSolid.conj.comps[j]? = some e'.conj := by simp [Graph.conj_comps, hj]
    have hO2 : Γ.swapSolid.conj.edgeIdx x .plus true = [i] := by rw [edgeIdx_conj]; exact hO
    have hI2 : Γ.swapSolid.conj.edgeIdx x .plus false = [j] := by rw [edgeIdx_conj]; exact hI
    have hM1 : Γ.swapSolid.conj.edgeIdx x .minus true = [] := by rw [edgeIdx_conj]; exact hO'
    have hM2 : Γ.swapSolid.conj.edgeIdx x .minus false = [] := by rw [edgeIdx_conj]; exact hI'
    have Ctx : GGCtxS C x Γ.swapSolid.conj i j e.conj e'.conj :=
      ⟨Graph.conj_Normal hN', Graph.conj_Plain hP', hx, Graph.conj_labelFree' hL', hO2, hI2, hM1,
        hM2, hi', hj'⟩
    have hX' : Γ.swapSolid.conj.xdotsAt x [i, j] = true := by
      refine xdotsAt_of_normal (Graph.conj_Normal hN') x [i, j] fun m hm => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact ⟨e.conj, hi', by rw [Ctx.espec.1]; rfl, Or.inl Ctx.espec.2.1⟩
      · exact ⟨e'.conj, hj', by rw [Ctx.e'spec.1]; rfl, Or.inr Ctx.e'spec.2.1⟩
    have hdeg' : Γ.swapSolid.conj.deg x = 2 := by rw [Graph.conj_deg']; exact hdeg
    have hnone : ggPos x Γ.swapSolid = none := by
      unfold ggPos
      rw [ite_eq_right (by simp [hdeg])]
      have : Γ.swapSolid.edgeIdx x .plus true = [] := hO'
      rw [this]
    have hE : oGGTT x Γ = (ggOut x Γ.swapSolid.conj i j e.conj e'.conj).conj.swapSolid.bind
        (fun _ g => oDotT g) := by
      unfold oGGTT
      rw [ite_eq_right (by simp [hpl]), hnone]
      simp only
      rw [ggPos_eq hdeg' hO2 hI2 hi' hj' hX']
    have hK'' : ∀ c ∈ Γ.swapSolid.conj.comps, c.kind.isRandom = true →
        (kAt true c).isRight = true := by
      intro c hc hr
      obtain ⟨d, hd, rfl⟩ := Graph.mem_conj_comps.1 hc
      rw [kAt_conj]
      exact hK' d hd (by simpa [Kind.conj_isRandom] using hr)
    have H : GGHyp true C x Γ.swapSolid.conj i j e.conj e'.conj :=
      ⟨Ctx, hK'', by rw [Graph.conj_wt]; exact hwt', hdeg'⟩
    refine ⟨_, hE, hswap _ (fun T hT => ?_), ?_⟩
    · obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
      exact (H.allTerms T₀ hT₀).conj
    · rw [hsl]
      unfold TExpansion.conj
      rw [List.length_map]
      exact (len_ggOut _ _ _ _ _ _).trans (by simp [Graph.conj_comps, Graph.swapSolid_comps'])

/-- The step of the transposed `GG` expansion at `x`: every output has the clauses `StepOut`. -/
theorem oGGTT_step {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C) (hP : Γ.Plain)
    (hL : Γ.LabelFree) (hK : Γ.RandomFirstInt) (hX : Γ.XdotApart) (hx : x.isRight = true)
    (hwt : Γ.wt x = 0) {y y' : Atom k n} (hin : Γ.GGInputAt x y y') :
    ∀ t ∈ oGGTT x Γ, StepOut Γ t := by
  obtain ⟨E, hE, hT, -⟩ := oGGTT_rep hN hP hL hK hx hwt hin
  rw [hE]
  exact bind_step hT hN hP hL hK hX

end GGTStep




section InDefs

variable {k n : ℕ} (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ) (e₁ : Comp (Atom k n))

/-- The indices of the solid edges of charge `plus` or `minus` entering `x` ([I, Def 3.11]). -/
def iXIdx : List ℕ := Γ.edgeIdx x .plus false ++ Γ.edgeIdx x .minus false

/-- The solid edge `G_{w₁ α}` taking the place of the first edge `G_{w₁ x}` of charge `plus`
entering `x` ([I, (3.13)]). -/
def iGw : Comp (Atom k (n + 1)) := mkC (.G .plus) (liftA 1 e₁.x) (newA 0)

/-- The components of a main term of [I, (3.13)] in case (iii): the edges `G_{w₁ x}` and `Ḡ_{w_j
x}` are exchanged for `s_{xα} G_{w₁ α} Ḡ_{w_j α}`. -/
def iBaseM (j : ℕ) : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++
    [oSx x, iGw e₁, mkC (.G .minus) (liftA 1 ((Γ.comps.getD j e₁).x)) (newA 0)]

/-- The components of the term of [I, (3.13)] in case (iii) in which `G_{w₁ x}` is exchanged for
`s_{xα} G_{w₁ α} G_{αx}`. -/
def iE1 : List (Comp (Atom k (n + 1))) :=
  liftCs 1 (Γ.comps.eraseIdx i₁) ++ [oSx x, iGw e₁, mkC (.G .plus) (newA 0) (liftA 1 x)]

/-- The components of the derivative terms of [I, (3.13)] in case (iii). -/
def iDs : List (List (Comp (Atom k (n + 1)))) :=
  (dTerms (liftA 1 x) (newA 0) (liftCs 1 (eraseIdxs (iXIdx x Γ) Γ.comps))).map fun d =>
    liftCs 1 (pickIdxs ((iXIdx x Γ).filter (· != i₁)) Γ.comps) ++ d ++ [oSx x, iGw e₁]

/-- The terms of `Ô^{(x)}_multi-e` in case (iii) of [I, Def 3.11], for the first edge `G_{w₁ x}`
of charge `plus` entering `x` (at the index `i₁`, the further such edges being at the indices
`is₂`). -/
def iOut : TExpansion k n :=
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

end InDefs

section InTerms

variable {k n : ℕ}

/-- The data of case (iii) of [I, Def 3.11]: `Γ` is plain and normal regular with bound `C`,
label-free, `x` is internal, no solid edge leaves `x`, and the edges of charge `plus` entering
`x` are at the indices `i₁ :: is₂`, the first being `e₁`. -/
structure InCtxS (C : ℕ) (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ)
    (e₁ : Comp (Atom k n)) : Prop where
  normal : Γ.Normal C
  plain : Γ.Plain
  right : x.isRight = true
  unl : ∀ c ∈ Γ.comps, c.label = none
  hIP : Γ.edgeIdx x .plus false = i₁ :: is₂
  hL : Γ.comps[i₁]? = some e₁
  hOP0 : Γ.edgeIdx x .plus true = []
  hOM0 : Γ.edgeIdx x .minus true = []

private theorem InCtxS.e₁spec {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : InCtxS C x Γ i₁ is₂ e₁) :
    e₁.kind = .G .plus ∧ e₁.y = x ∧ e₁.x ≠ x := by
  have h : i₁ ∈ Γ.edgeIdx x .plus false := by rw [Ctx.hIP]; exact List.mem_cons_self ..
  obtain ⟨c, hc, hk, ho⟩ := mem_edgeIdx.1 h
  rw [Ctx.hL] at hc
  obtain rfl := Option.some.inj hc
  exact ⟨hk, ho⟩

private theorem InCtxS.e₁mem {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : InCtxS C x Γ i₁ is₂ e₁) : e₁ ∈ Γ.comps :=
  List.mem_of_getElem? Ctx.hL

theorem mem_iXIdx {Γ : Graph k n} {x : Atom k n} {j : ℕ} :
    j ∈ iXIdx x Γ ↔ ∃ c, Γ.comps[j]? = some c ∧ ∃ ch, c.kind = .G ch ∧ (c.y = x ∧ c.x ≠ x) := by
  unfold iXIdx
  simp only [List.mem_append, mem_edgeIdx]
  constructor
  · rintro (⟨c, h1, h2, h3⟩ | ⟨c, h1, h2, h3⟩)
    · exact ⟨c, h1, _, h2, h3⟩
    · exact ⟨c, h1, _, h2, h3⟩
  · rintro ⟨c, h1, ch, h2, h3⟩
    cases ch
    · exact Or.inl ⟨c, h1, h2, h3⟩
    · exact Or.inr ⟨c, h1, h2, h3⟩

private theorem iXIdx_nodup (x : Atom k n) (Γ : Graph k n) : (iXIdx x Γ).Nodup := by
  unfold iXIdx
  have n3 := edgeIdx_nodup Γ x .plus false
  have n4 := edgeIdx_nodup Γ x .minus false
  simp only [List.nodup_append]
  refine ⟨n3, n4, ?_⟩
  intro a ha b hb hab
  subst hab
  exact edgeIdx_disjoint (Or.inl (by simp)) ha hb

private theorem iXIdx_mem_i₁ {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : InCtxS C x Γ i₁ is₂ e₁) : i₁ ∈ iXIdx x Γ := by
  have : i₁ ∈ Γ.edgeIdx x .plus false := by rw [Ctx.hIP]; exact List.mem_cons_self ..
  unfold iXIdx
  simp [this]

private theorem ixe_fL_perm {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : InCtxS C x Γ i₁ is₂ e₁) :
    (pickIdxs ((iXIdx x Γ).filter (· != i₁)) Γ.comps ++ eraseIdxs (iXIdx x Γ) Γ.comps ++
      [e₁]).Perm Γ.comps := by
  have hnd := iXIdx_nodup x Γ
  have hmem := iXIdx_mem_i₁ Ctx
  have hP1 := pickIdxs_perm ((iXIdx x Γ).filter (· != i₁))
    (hnd.sublist (List.filter_sublist)) Γ.comps
  have hP2 := pickIdxs_perm (iXIdx x Γ) hnd Γ.comps
  have hxI : (iXIdx x Γ).Perm (i₁ :: (iXIdx x Γ).filter (· != i₁)) := by
    have := List.perm_cons_erase hmem
    rwa [hnd.erase_eq_filter] at this
  have hP3 := hxI.filterMap (fun i => Γ.comps[i]?)
  simp only [List.filterMap_cons, Ctx.hL] at hP3
  have hall : (pickIdxs (iXIdx x Γ) Γ.comps).Perm
      (e₁ :: pickIdxs ((iXIdx x Γ).filter (· != i₁)) Γ.comps) :=
    hP2.trans (hP3.trans (hP1.symm.cons e₁))
  have h1 := eraseIdxs_pick_perm (iXIdx x Γ) Γ.comps
  refine List.Perm.trans ?_ ((hall.symm.append_left _).trans h1)
  exact perm_aux _ _ _

private theorem fL_untouched_in {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (Ctx : InCtxS C x Γ i₁ is₂ e₁)
    {c : Comp (Atom k n)} (hc : c ∈ eraseIdxs (iXIdx x Γ) Γ.comps) {ch : Charge}
    (hk : c.kind = .G ch) : c.x ≠ x ∧ c.y ≠ x := by
  obtain ⟨i, hi, hn⟩ := mem_eraseIdxs_iff.1 hc
  have hcm : c ∈ Γ.comps := mem_eraseIdxs_of_mem hc
  have hsl := Ctx.normal.2.1 c hcm (by simp [hk, Kind.isSolid])
  constructor
  · intro hcx
    have hy : c.y ≠ x := by rw [← hcx]; exact fun h => hsl h.symm
    have : i ∈ Γ.edgeIdx x ch true := mem_edgeIdx.2 ⟨c, hi, hk, hcx, hy⟩
    cases ch
    · rw [Ctx.hOP0] at this; simp at this
    · rw [Ctx.hOM0] at this; simp at this
  · intro hcy
    exact hn (mem_iXIdx.2 ⟨c, hi, ch, hk, hcy, by rw [← hcy]; exact hsl⟩)

end InTerms


section HatCopies

variable {k n : ℕ}


theorem InCtxS.conj_of {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hN : Γ.Normal C) (hP : Γ.Plain) (hx : x.isRight = true)
    (hU : ∀ c ∈ Γ.comps, c.label = none) (hIP : Γ.edgeIdx x .minus false = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (hOP0 : Γ.edgeIdx x .plus true = [])
    (hOM0 : Γ.edgeIdx x .minus true = []) : InCtxS C x Γ.conj i₁ is₂ e₁.conj where
  normal := Graph.conj_Normal hN
  plain := Graph.conj_Plain hP
  right := hx
  unl := fun c' hc' => by
    obtain ⟨c, hc, rfl⟩ := Graph.mem_conj_comps.1 hc'
    simpa using hU c hc
  hIP := by rw [edgeIdx_conj]; exact hIP
  hL := by simp [Graph.conj_comps, hL]
  hOP0 := by rw [edgeIdx_conj]; exact hOM0
  hOM0 := by rw [edgeIdx_conj]; exact hOP0


theorem multiEOut_eq {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hOP : Γ.edgeIdx x .plus true = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (hX : Γ.xdotsAt x (oXIdx x Γ) = true) :
    multiEOut x Γ = some (oOut x Γ i₁ is₂ e₁) := by
  unfold multiEOut
  split
  · rename_i h
    rw [hOP] at h
    cases h
  · rename_i i₁' is₂' h
    rw [hOP] at h
    obtain ⟨rfl, rfl⟩ := List.cons.inj h
    split
    · rename_i h2
      rw [hL] at h2
      cases h2
    · rename_i e₁' h2
      rw [hL] at h2
      obtain rfl := Option.some.inj h2
      dsimp only
      rw [ite_eq_right (by simpa [oXIdx] using hX)]
      rfl

theorem multiEIn_eq {x : Atom k n} {Γ : Graph k n} {i₁ : ℕ} {is₂ : List ℕ}
    {e₁ : Comp (Atom k n)} (hIP : Γ.edgeIdx x .plus false = i₁ :: is₂)
    (hL : Γ.comps[i₁]? = some e₁) (hX : Γ.xdotsAt x (iXIdx x Γ) = true) :
    multiEIn x Γ = some (iOut x Γ i₁ is₂ e₁) := by
  unfold multiEIn
  split
  · rename_i h
    rw [hIP] at h
    cases h
  · rename_i i₁' is₂' h
    rw [hIP] at h
    obtain ⟨rfl, rfl⟩ := List.cons.inj h
    split
    · rename_i h2
      rw [hL] at h2
      cases h2
    · rename_i e₁' h2
      rw [hL] at h2
      obtain rfl := Option.some.inj h2
      dsimp only
      rw [ite_eq_right (by simpa [iXIdx] using hX)]
      rfl

theorem edge_of_idx {Γ : Graph k n} {x : Atom k n} {ch : Charge} {out : Bool} {i : ℕ}
    (h : i ∈ Γ.edgeIdx x ch out) : ∃ e, Γ.comps[i]? = some e := by
  obtain ⟨c, hc, -⟩ := mem_edgeIdx.1 h
  exact ⟨c, hc⟩

end HatCopies

/-! ## Degrees and standard neutral atoms from signatures -/

section Sig

variable {k n : ℕ}

/-- The kind of a component and which of its ends are at `u`. -/
private def sigF {m : ℕ} (u : Atom k m) (c : Comp (Atom k m)) : Kind × Bool × Bool :=
  (c.kind, decide (c.x = u), decide (c.y = u))

/-- The non-`×`-dotted components at `u`. -/
private def locL {m : ℕ} (g : Graph k m) (u : Atom k m) : List (Comp (Atom k m)) :=
  g.comps.filter fun c => atB u c && c.kind != .xdot

/-- The end at `u` of a solid component, from its signature. -/
private def endS : Kind × Bool × Bool → Option (Bool × Charge)
  | (.G ch, true, false) => some (true, ch)
  | (.G ch, false, true) => some (false, ch)
  | _ => none

private theorem ends_eq_locL {m : ℕ} (g : Graph k m) (u : Atom k m) :
    g.ends u = ((locL g u).map (sigF u)).filterMap endS := by
  unfold Graph.ends locL
  rw [List.filterMap_map, List.filterMap_filter]
  congr 1
  funext c
  rcases c with ⟨κ, a, b, mi, l⟩
  cases κ <;> by_cases h1 : a = u <;> by_cases h2 : b = u <;>
    simp [atB, endS, sigF, h1, h2, Function.comp]

/-- Two graphs whose non-`×`-dotted components at `u'` and `u` have the same signatures, up to
order, have the same degree and standard neutral status there. -/
private theorem local_sig_transfer {m m' : ℕ} {g : Graph k m} {g' : Graph k m'} {u : Atom k m}
    {u' : Atom k m'} (h : ((locL g' u').map (sigF u')).Perm ((locL g u).map (sigF u))) :
    g'.deg u' = g.deg u ∧ g'.stdNeutralAt u' = g.stdNeutralAt u := by
  have hcnt : ∀ (P : Kind → Bool) {m₀ : ℕ} (g₀ : Graph k m₀) (u₀ : Atom k m₀),
      ((locL g₀ u₀).filter fun c => P c.kind).length =
        (((locL g₀ u₀).map (sigF u₀)).filter fun s => P s.1).length := by
    intro P m₀ g₀ u₀
    rw [List.filter_map, List.length_map]
    rfl
  have hdeg : ∀ {m₀ : ℕ} (g₀ : Graph k m₀) (u₀ : Atom k m₀),
      g₀.deg u₀ = ((locL g₀ u₀).filter fun c => c.kind.isSolid).length := by
    intro m₀ g₀ u₀
    unfold Graph.deg locL
    rw [List.filter_filter]
    congr 1
    apply List.filter_congr
    intro c _
    cases hk : c.kind <;> simp [hk, Kind.isSolid, atB, Bool.and_comm]
  refine ⟨?_, ?_⟩
  · rw [hdeg, hdeg, hcnt, hcnt, (h.filter _).length_eq]
  · rw [std_eq, std_eq]
    have e : ∀ {m₀ : ℕ} (g₀ : Graph k m₀) (u₀ : Atom k m₀),
        ((g₀.comps.filter (atB u₀)).filter fun c => c.kind != .xdot) = locL g₀ u₀ := by
      intro m₀ g₀ u₀; unfold locL; rw [List.filter_filter]; congr 1; funext c
      exact Bool.and_comm _ _
    rw [e, e, ends_eq_locL, ends_eq_locL, stdM_perm (h.filterMap _)]
    have hl : (locL g' u').length = (locL g u).length := by
      have := h.length_eq; simpa using this
    rw [hl, hcnt (fun κ => κ.isSolid) g' u', hcnt (fun κ => κ.isSolid) g u,
      hcnt (fun κ => κ == .waved .s) g' u', hcnt (fun κ => κ == .waved .s) g u,
      (h.filter _).length_eq, (h.filter (fun s => s.1 == .waved .s)).length_eq]

/-- The local signatures of a term without labels at a moved atom. -/
private theorem Sch.local_sig {j : ℕ} {Γ : Graph k n} {R : List (Comp (Atom k n))}
    {N : List (Comp (Atom k (n + j)))} {g : Graph k (n + j)} (hS : Sch Γ j R N none g)
    (u : Atom k n)
    (hRN : ((N.filter fun c => atB (liftA j u) c && c.kind != .xdot).map (sigF (liftA j u))).Perm
      ((R.filter fun c => atB u c && c.kind != .xdot).map (sigF u))) :
    g.deg (liftA j u) = Γ.deg u ∧ g.stdNeutralAt (liftA j u) = Γ.stdNeutralAt u := by
  obtain ⟨-, K, h1, h2⟩ := hS
  apply local_sig_transfer
  unfold locL
  refine ((h2.filter _).map _).trans ?_
  refine List.Perm.trans ?_ ((h1.filter _).map _).symm
  rw [show (liftCs j K ++ N).map (labF none) = liftCs j K ++ N from List.map_id _]
  rw [List.filter_append, List.filter_append, List.map_append, List.map_append]
  refine List.Perm.append (List.Perm.of_eq ?_) hRN
  unfold liftCs
  rw [List.filter_map, List.map_map]
  have e1 : ((fun c => atB (liftA j u) c && c.kind != .xdot) ∘ Comp.map (liftA j)) =
      (fun c : Comp (Atom k n) => atB u c && c.kind != .xdot) := by
    funext c; simp [Function.comp, atB, Comp.map, beq_liftA]
  have e2 : (sigF (liftA j u) ∘ Comp.map (liftA j)) = sigF u := by
    funext c; simp [Function.comp, sigF, Comp.map]
  rw [e1, e2]

end Sig

/-! ## Moving two solid edges from `x` to a new atom -/

section Reattach

variable {k n : ℕ}

/-- The component `e` with its end `x` moved to the new atom `α`. -/
private def rxC (x : Atom k n) (e : Comp (Atom k n)) : Comp (Atom k (n + 1)) :=
  mkC e.kind (if e.x = x then newA 0 else liftA 1 e.x) (if e.y = x then newA 0 else liftA 1 e.y)

private theorem rxC_sig {x u : Atom k n} {e : Comp (Atom k n)} (hu : u ≠ x) :
    sigF (liftA 1 u) (rxC x e) = sigF u e := by
  unfold sigF rxC mkC
  simp only
  congr 2
  · by_cases h : e.x = x
    · simp [h, Ne.symm hu]
    · simp [h]
  · by_cases h : e.y = x
    · simp [h, Ne.symm hu]
    · simp [h]

private theorem rxC_atB {x u : Atom k n} {e : Comp (Atom k n)} (hu : u ≠ x) :
    atB (liftA 1 u) (rxC x e) = atB u e := by
  unfold atB rxC mkC
  simp only
  have key : ∀ a : Atom k n, ((if a = x then newA 0 else liftA 1 a) == liftA 1 u) = (a == u) := by
    intro a
    by_cases h : a = x
    · rw [if_pos h, h]
      have : (x == u) = false := by simpa using Ne.symm hu
      rw [this]
      simp
    · rw [if_neg h, beq_liftA]
  rw [key, key]

/-- The potential decreases at a main term of the multi-edge expansion: two solid edges at `x`
are moved to a new atom `α` joined to `x` by `s_{xα}`. If `x` has degree at least `3`, the excess
degree of `x` drops; if `x` has degree `2`, it is not standard neutral and `α` is. -/
private theorem phi_reattach {C : ℕ} {Γ : Graph k n} {x : Atom k n} {e₁ e₂ : Comp (Atom k n)}
    {g : Graph k (n + 1)}
    (hS : Sch Γ 1 [e₁, e₂] [mkC (.waved .s) (liftA 1 x) (newA 0), rxC x e₁, rxC x e₂] none g)
    (hN : Γ.Normal C) (hx : x.isRight = true) (he₁ : e₁ ∈ Γ.comps) (he₂ : e₂ ∈ Γ.comps)
    (hs₁ : e₁.kind.isSolid = true) (hs₂ : e₂.kind.isSolid = true)
    (hx₁ : e₁.x = x ∨ e₁.y = x) (hx₂ : e₂.x = x ∨ e₂.y = x)
    (HM : 3 ≤ Γ.deg x ∨ (Γ.stdNeutralAt x = false ∧ g.stdNeutralAt (newA 0) = true)) :
    g.phi + 3 ≤ Γ.phi := by
  have hne₁ := hN.2.1 e₁ he₁ hs₁
  have hne₂ := hN.2.1 e₂ he₂ hs₂
  have hlt : ∀ (e : Comp (Atom k n)), e.kind.isSolid = true → (rxC x e).kind.isLt = false := by
    intro e h; simp [rxC, mkC]; revert h; cases e.kind <;> simp [Kind.isSolid, Kind.isLt]
  have hrg : ∀ (e : Comp (Atom k n)), e.kind.isSolid = true → (rxC x e).kind.isRg = false := by
    intro e h; simp [rxC, mkC]; revert h; cases e.kind <;> simp [Kind.isSolid, Kind.isRg]
  have hlw := hS.lwN
  have hrw := hS.rwN
  have e1 : e₁.kind.isLt = false := by revert hs₁; cases e₁.kind <;> simp [Kind.isSolid, Kind.isLt]
  have e2 : e₂.kind.isLt = false := by revert hs₂; cases e₂.kind <;> simp [Kind.isSolid, Kind.isLt]
  have f1 : e₁.kind.isRg = false := by revert hs₁; cases e₁.kind <;> simp [Kind.isSolid, Kind.isRg]
  have f2 : e₂.kind.isRg = false := by revert hs₂; cases e₂.kind <;> simp [Kind.isSolid, Kind.isRg]
  have w1 : (mkC (.waved .s) (liftA 1 x) (newA 0) : Comp (Atom k (n + 1))).kind.isLt = false := rfl
  have w2 : (mkC (.waved .s) (liftA 1 x) (newA 0) : Comp (Atom k (n + 1))).kind.isRg = false := rfl
  simp only [List.filter_cons, List.filter_nil, e1, e2, f1, f2, hlt e₁ hs₁, hlt e₂ hs₂,
    hrg e₁ hs₁, hrg e₂ hs₂, w1, w2, Bool.false_eq_true, ite_false, List.length_nil,
    add_zero] at hlw hrw
  -- degree of `x`
  have hdx := hS.deg x
  have hrx : ∀ e : Comp (Atom k n), (e.x = x ∨ e.y = x) → e.x ≠ e.y →
      atB (liftA 1 x) (rxC x e) = false := by
    intro e h1 h2
    unfold atB rxC mkC
    rcases h1 with h | h
    · have : e.y ≠ x := by rw [← h]; exact Ne.symm h2
      simp [h, this, beq_liftA]
    · have : e.x ≠ x := by rw [← h]; exact h2
      simp [h, this, beq_liftA]
  have ha1 : atB x e₁ = true := by rcases hx₁ with h | h <;> simp [atB, h]
  have ha2 : atB x e₂ = true := by rcases hx₂ with h | h <;> simp [atB, h]
  have hk1 : (rxC x e₁).kind.isSolid = true := by simpa [rxC, mkC] using hs₁
  have hk2 : (rxC x e₂).kind.isSolid = true := by simpa [rxC, mkC] using hs₂
  have w3 : (mkC (.waved .s) (liftA 1 x) (newA 0) : Comp (Atom k (n + 1))).kind.isSolid = false :=
    rfl
  simp only [List.filter_cons, List.filter_nil, hs₁, hs₂, ha1, ha2, hk1, hk2, w3,
    hrx e₁ hx₁ hne₁, hrx e₂ hx₂ hne₂, Bool.and_true, Bool.and_false, Bool.true_and,
    Bool.false_and, ite_true, ite_false, Bool.false_eq_true, List.length_cons,
    List.length_nil] at hdx
  -- degree of `α`
  have hnew : ∀ e : Comp (Atom k n), (e.x = x ∨ e.y = x) → atB (newA 0) (rxC x e) = true := by
    intro e h
    rcases h with h | h <;> simp [atB, rxC, mkC, h]
  have hda := hS.deg_new 0
  simp only [List.filter_cons, List.filter_nil, hk1, hk2, w3, hnew e₁ hx₁, hnew e₂ hx₂,
    Bool.and_true, Bool.false_and, ite_true, ite_false, Bool.false_eq_true, List.length_cons,
    List.length_nil] at hda
  -- the original atoms other than `x`
  have hloc : ∀ u : Atom k n, u ≠ x →
      g.deg (liftA 1 u) = Γ.deg u ∧ g.stdNeutralAt (liftA 1 u) = Γ.stdNeutralAt u := by
    intro u hu
    refine hS.local_sig u (List.Perm.of_eq ?_)
    have hsx : (atB (liftA 1 u) (mkC (.waved .s) (liftA 1 x) (newA 0)) &&
        (mkC (.waved .s) (liftA 1 x) (newA 0) : Comp (Atom k (n + 1))).kind != .xdot) = false := by
      simp [atB, mkC, beq_liftA, Ne.symm hu]
    have hx1 : (e₁.kind != .xdot) = true := by revert hs₁; cases e₁.kind <;> simp [Kind.isSolid]
    have hx2 : (e₂.kind != .xdot) = true := by revert hs₂; cases e₂.kind <;> simp [Kind.isSolid]
    have hr1 : ((rxC x e₁).kind != .xdot) = true := by simpa [rxC, mkC] using hx1
    have hr2 : ((rxC x e₂).kind != .xdot) = true := by simpa [rxC, mkC] using hx2
    simp only [List.filter_cons, List.filter_nil, hsx, rxC_atB hu, hr1, hr2, hx1, hx2,
      Bool.and_true, Bool.false_eq_true, ite_false]
    split_ifs <;> simp [rxC_sig hu]
  obtain ⟨ix, rfl⟩ : ∃ ix, x = .inr ix := by
    rcases x with a | a
    · simp at hx
    · exact ⟨a, rfl⟩
  have hX := sum_one_eq (fun i => g.deg (liftA 1 (.inr i)) - 2) (fun i => Γ.deg (.inr i) - 2) ix
    (fun i h => by simp only [(hloc (.inr i) (fun e => h (Sum.inr.inj e))).1])
  have hB := sum_one_eq (fun i => badI g (liftA 1 (.inr i))) (fun i => badI Γ (.inr i)) ix
    (fun i h => by
      simp only [badI, (hloc (.inr i) (fun e => h (Sum.inr.inj e))).1,
        (hloc (.inr i) (fun e => h (Sum.inr.inj e))).2])
  have hgX := degX_lift (j := 1) g
  have hgB := badN_lift (j := 1) g
  simp only [Fin.sum_univ_one] at hgX hgB
  have hΓX : Γ.degX = ∑ i : Fin n, (Γ.deg (.inr i) - 2) := rfl
  rw [← badN_eq] at hB
  unfold Graph.phi
  rw [hlw, hrw]
  have hbα : badI g (newA 0) ≤ 1 := by unfold badI; split_ifs <;> simp
  have hbx : badI g (liftA 1 (.inr ix)) ≤ 1 := by unfold badI; split_ifs <;> simp
  rcases HM with H3 | ⟨hsx, hsα⟩
  · omega
  · have hd2 : Γ.deg (.inr ix) = 2 ∨ 3 ≤ Γ.deg (.inr ix) := by omega
    rcases hd2 with hd2 | H3
    · have b1 : badI Γ (.inr ix) = 1 := by simp [badI, hd2, hsx]
      have b2 : badI g (liftA 1 (.inr ix)) = 0 := by simp [badI]; omega
      have b3 : badI g (newA 0) = 0 := by simp [badI, hsα]
      rw [b1] at hB
      rw [hda] at hgX
      omega
    · omega

end Reattach

/-! ## The main terms of the multi-edge expansion -/

section MEBase

variable {k n : ℕ}

private theorem rxC_of_x {x : Atom k n} {e : Comp (Atom k n)} (h1 : e.x = x) (h2 : e.y ≠ x) :
    rxC x e = mkC e.kind (newA 0) (liftA 1 e.y) := by
  simp [rxC, h1, h2]

private theorem rxC_of_y {x : Atom k n} {e : Comp (Atom k n)} (h1 : e.y = x) (h2 : e.x ≠ x) :
    rxC x e = mkC e.kind (liftA 1 e.x) (newA 0) := by
  simp [rxC, h1, h2]

private theorem rxC_facts {x : Atom k n} {e : Comp (Atom k n)} (hx : x.isRight = true)
    (hs : e.kind.isSolid = true) (hxe : e.x = x ∨ e.y = x) (hne : e.x ≠ e.y)
    (hK : e.x.isRight = true) :
    NewOK (rxC x e) ∧ (rxC x e).label = none ∧ (rxC x e).x.isRight = true ∧
    atB (newA 0) (rxC x e) = true ∧ (isNewA n (rxC x e).x || isNewA n (rxC x e).y) = true ∧
    ((rxC x e).x.isLeft || (rxC x e).y.isLeft) = (e.x.isLeft || e.y.isLeft) ∧
    (rxC x e).kind.isSolid = true ∧ (rxC x e).kind.isRandom = true ∧ (rxC x e).kind.ord = 1 := by
  have hxL : x.isLeft = false := by cases x <;> simp_all
  have hk : ∃ ch, e.kind = .G ch := by revert hs; cases e.kind <;> simp [Kind.isSolid]
  obtain ⟨ch, hch⟩ := hk
  rcases hxe with h | h
  · have hy : e.y ≠ x := by rw [← h]; exact Ne.symm hne
    rw [rxC_of_x h hy, hch]
    refine ⟨NewOK_G _ (by simp), rfl, rfl, by simp [atB, mkC], by simp [mkC], ?_, ?_, ?_, ?_⟩
    · simp [mkC, h, hxL]
    · simp [mkC, Kind.isSolid]
    · simp [mkC, Kind.isRandom]
    · simp [mkC, Kind.ord]
  · have hy : e.x ≠ x := by rw [← h]; exact hne
    rw [rxC_of_y h hy, hch]
    refine ⟨NewOK_G _ (by simp), rfl, by simpa [mkC] using hK, by simp [atB, mkC], by simp [mkC],
      ?_, ?_, ?_, ?_⟩
    · simp [mkC, h, hxL]
    · simp [mkC, Kind.isSolid]
    · simp [mkC, Kind.isRandom]
    · simp [mkC, Kind.ord]

/-- The main terms `s_{xα} G_{α ·} G_{α ·}` of the multi-edge expansion, with an optional light
weight or labelled weight on `x`. -/
private theorem termBase {C : ℕ} {Γ : Graph k n} {x : Atom k n} {K : List (Comp (Atom k n))}
    {e₁ e₂ : Comp (Atom k n)} (hN : Γ.Normal C) (hK₀ : Γ.RandomFirstInt) (hx : x.isRight = true)
    (hKR : Γ.comps.Perm (K ++ [e₁, e₂])) (he₁ : e₁ ∈ Γ.comps) (he₂ : e₂ ∈ Γ.comps)
    (hs₁ : e₁.kind.isSolid = true) (hs₂ : e₂.kind.isSolid = true)
    (hx₁ : e₁.x = x ∨ e₁.y = x) (hx₂ : e₂.x = x ∨ e₂.y = x)
    (lab : Option (Atom k (n + 1))) (extra : List (Comp (Atom k (n + 1))))
    (hex : (extra = [] ∧ lab = none) ∨ (∃ ch, extra = [mkC (.light ch) (liftA 1 x) (liftA 1 x)] ∧
      lab = none) ∨ (∃ ch, extra = [mkC (.weight ch) (liftA 1 x) (liftA 1 x)] ∧
      lab = some (liftA 1 x)))
    (HM : 3 ≤ Γ.deg x ∨ (Γ.stdNeutralAt x = false ∧
      (⟨liftCs 1 K ++ [mkC (.waved .s) (liftA 1 x) (newA 0), rxC x e₁, rxC x e₂], 1⟩ :
        Graph k (n + 1)).stdNeutralAt (newA 0) = true))
    (co : Coeff) :
    TermOK Γ x (t1 (labW lab (liftCs 1 K ++ ([mkC (.waved .s) (liftA 1 x) (newA 0), rxC x e₁,
      rxC x e₂] ++ extra))) co) := by
  have hne₁ := hN.2.1 e₁ he₁ hs₁
  have hne₂ := hN.2.1 e₂ he₂ hs₂
  have hr₁ : e₁.kind.isRandom = true := by revert hs₁; cases e₁.kind <;> simp [Kind.isSolid, Kind.isRandom]
  have hr₂ : e₂.kind.isRandom = true := by revert hs₂; cases e₂.kind <;> simp [Kind.isSolid, Kind.isRandom]
  have hxR : (liftA 1 x).isRight = true := by simpa using hx
  -- the other ends of `e₁`, `e₂`
  have hy : ∀ e : Comp (Atom k n), e ∈ Γ.comps → e.kind.isSolid = true → (e.x = x ∨ e.y = x) →
      e.x ≠ e.y → ∃ y, y ≠ x ∧ (rxC x e = mkC e.kind (newA 0) (liftA 1 y) ∧ e.x = x ∧ e.y = y ∨
        rxC x e = mkC e.kind (liftA 1 y) (newA 0) ∧ e.y = x ∧ e.x = y ∧ y.isRight = true) := by
    intro e he hs hxe hne
    rcases hxe with h | h
    · have : e.y ≠ x := by rw [← h]; exact Ne.symm hne
      exact ⟨e.y, this, Or.inl ⟨rxC_of_x h this, h, rfl⟩⟩
    · have : e.x ≠ x := by rw [← h]; exact hne
      have hr : e.kind.isRandom = true := by revert hs; cases e.kind <;> simp [Kind.isSolid, Kind.isRandom]
      exact ⟨e.x, this, Or.inr ⟨rxC_of_y h this, h, rfl, hK₀ e he hr⟩⟩
  obtain ⟨y₁, hy₁x, hy₁⟩ := hy e₁ he₁ hs₁ hx₁ hne₁
  obtain ⟨y₂, hy₂x, hy₂⟩ := hy e₂ he₂ hs₂ hx₂ hne₂
  have hsx : (mkC (.waved .s) (liftA 1 x) (newA 0) : Comp (Atom k (n + 1))).kind.isRandom = false :=
    rfl
  obtain ⟨n1, l1, k1, a1, w1, x1, s1, r1, o1⟩ := rxC_facts hx hs₁ hx₁ hne₁ (hK₀ e₁ he₁ hr₁)
  obtain ⟨n2, l2, k2, a2, w2, x2, s2, r2, o2⟩ := rxC_facts hx hs₂ hx₂ hne₂ (hK₀ e₂ he₂ hr₂)
  have hxL : x.isLeft = false := by cases x <;> simp_all
  have hex' : ∀ c ∈ extra, NewOK c ∧ c.label = none ∧ c.x = liftA 1 x ∧ c.kind.isSolid = false ∧
      c.kind.isRandom = true ∧ ¬ atB (newA 0) c = true := by
    intro c hc
    rcases hex with ⟨rfl, -⟩ | ⟨ch, rfl, -⟩ | ⟨ch, rfl, -⟩ <;> simp at hc <;> subst hc
    · exact ⟨NewOK_light _ _, rfl, rfl, rfl, rfl, by simp [atB, mkC]⟩
    · exact ⟨NewOK_weight _ _, rfl, rfl, rfl, rfl, by simp [atB, mkC]⟩
  have hexs : (extra.filter fun c => c.kind.isSolid).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc; simp [(hex' c hc).2.2.2.1]
  have hexo : ordL extra = 0 ∨ ordL extra = 1 := by
    rcases hex with ⟨rfl, -⟩ | ⟨ch, rfl, -⟩ | ⟨ch, rfl, -⟩ <;> simp [ordL, mkC, Kind.ord]
  refine termOK_mk (K := K) (R := [e₁, e₂]) lab
    ([mkC (.waved .s) (liftA 1 x) (newA 0), rxC x e₁, rxC x e₂] ++ extra) [] co
    (ordL extra).toNat hKR (by simp [hr₁, hr₂]) (by simp) (by simp) ?_ ?_
    ?_ ?_ (fun _ _ => false) (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl) | hc
    · exact ⟨NewOK_waved _ _ _, rfl⟩
    · exact ⟨n1, l1⟩
    · exact ⟨n2, l2⟩
    · exact ⟨(hex' c hc).1, (hex' c hc).2.1⟩
  · intro c hc hr
    simp only [List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl) | hc
    · simp [mkC, Kind.isRandom] at hr
    · exact k1
    · exact k2
    · rw [(hex' c hc).2.2.1]; exact hxR
  · have h1 : e₁.kind.ord = 1 := by
      obtain ⟨ch, h⟩ : ∃ ch, e₁.kind = .G ch := by revert hs₁; cases e₁.kind <;> simp [Kind.isSolid]
      rw [h]; rfl
    have h2 : e₂.kind.ord = 1 := by
      obtain ⟨ch, h⟩ : ∃ ch, e₂.kind = .G ch := by revert hs₂; cases e₂.kind <;> simp [Kind.isSolid]
      rw [h]; rfl
    have : (Kind.waved Wave.s).ord = 2 := rfl
    simp only [List.append_nil, ordL_append, ordL_cons, ordL_nil, o1, o2, h1, h2, mkC, this]
    rcases hexo with h | h <;> rw [h] <;> norm_num
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have w3 : (mkC (.waved .s) (liftA 1 x) (newA 0) : Comp (Atom k (n + 1))).kind.isSolid = false :=
      rfl
    have h0 : (extra.filter fun c => c.kind.isSolid && atB (newA 0) c).length = 0 := by
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro c hc; simp [(hex' c hc).2.2.2.1]
    simp only [List.append_nil, List.filter_append, List.length_append, List.filter_cons,
      List.filter_nil, s1, s2, a1, a2, w3, Bool.and_true, Bool.false_and, Bool.false_eq_true,
      ite_false, ite_true, h0, List.length_cons, List.length_nil]
    omega
  · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    simp only [List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl) | hc
    · simp [mkC, Kind.isSolid]
    · revert w1; cases isNewA n (rxC x e₁).x <;> cases isNewA n (rxC x e₁).y <;> simp
    · revert w2; cases isNewA n (rxC x e₂).x <;> cases isNewA n (rxC x e₂).y <;> simp
    · simp [(hex' c hc).2.2.2.1]
  · simp only [List.append_nil, List.filter_append, List.length_append, List.filter_cons,
      List.filter_nil, s1, s2, hexs]
    simp [mkC, Kind.isSolid]
  · intro _
    simp only [List.append_nil, List.filter_append, List.length_append, List.filter_cons,
      List.filter_nil, s1, s2, hexs]
    simp [mkC, Kind.isSolid]
  · have w3 : (mkC (.waved .s) (liftA 1 x) (newA 0) : Comp (Atom k (n + 1))).kind.isSolid = false :=
      rfl
    have h0 : (extra.filter fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length = 0 := by
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro c hc; simp [(hex' c hc).2.2.2.1]
    simp only [List.append_nil, List.filter_append, List.length_append, List.filter_cons,
      List.filter_nil, s1, s2, x1, x2, w3, hs₁, hs₂, Bool.true_and, Bool.false_and,
      Bool.false_eq_true, ite_false, h0, add_zero, List.length_nil]
    split_ifs <;> simp
  · intro hl hs0
    have hx0 : extra = [] := by
      rcases hex with ⟨h, -⟩ | ⟨ch, rfl, -⟩ | ⟨ch, -, h⟩
      · exact h
      · simp [ordL, mkC, Kind.ord] at hs0
      · rw [h] at hl; cases hl
    subst hx0 hl
    have hS : Sch Γ 1 [e₁, e₂] [mkC (.waved .s) (liftA 1 x) (newA 0), rxC x e₁, rxC x e₂] none
        ⟨labW none (liftCs 1 K ++ ([mkC (.waved .s) (liftA 1 x) (newA 0), rxC x e₁, rxC x e₂] ++ [])),
          co⟩ :=
      sch_mk (by simp [hr₁, hr₂]) hKR none [mkC (.waved .s) (liftA 1 x) (newA 0), rxC x e₁, rxC x e₂]
        [] (by simp) (by simp [labW]) co
    exact phi_reattach hS hN hx he₁ he₂ hs₁ hs₂ hx₁ hx₂ HM
  · intro hl
    refine ⟨labF lab (rxC x e₁), ?_, by rw [labF_kind]; exact r1⟩
    simp only [labW_eq_map, List.append_nil]
    exact List.mem_map_of_mem (by simp)
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    refine sameMol_of_waved (w := .s) ?_ hxR rfl
    simp only [labW_eq_map, List.append_nil]
    refine List.mem_map.2 ⟨mkC (.waved .s) (liftA 1 x) (newA 0), by simp, ?_⟩
    exact labF_nonrandom lab rfl

/-- The terms `s_{xα} G_{·α} G_{α ·}` replacing one solid edge `e₁` at `x` (the terms with the
factor `(k₁ - 1)`, `k₄` or `(k₃ - 1)` of [I, (3.13), (3.14)]), without or with the label `Q_x`. -/
private theorem termE1 {C : ℕ} {Γ : Graph k n} {x : Atom k n} {K : List (Comp (Atom k n))}
    {e₁ : Comp (Atom k n)} (hN : Γ.Normal C) (hK₀ : Γ.RandomFirstInt) (hx : x.isRight = true)
    (hKR : Γ.comps.Perm (K ++ [e₁])) (he₁ : e₁ ∈ Γ.comps) (hs₁ : e₁.kind.isSolid = true)
    (hx₁ : e₁.x = x ∨ e₁.y = x) (c₀ : Comp (Atom k (n + 1))) (ch : Charge)
    (hc₀ : c₀ = mkC (.G ch) (liftA 1 x) (newA 0) ∨ c₀ = mkC (.G ch) (newA 0) (liftA 1 x))
    (lab : Option (Atom k (n + 1))) (hlab : lab = none ∨ lab = some (liftA 1 x))
    (cs : List (Comp (Atom k (n + 1))))
    (hcs : cs.Perm (labW lab (liftCs 1 K ++ [mkC (.waved .s) (liftA 1 x) (newA 0), c₀, rxC x e₁])))
    (co : Coeff) : TermOK Γ x (t1 cs co) := by
  have hne₁ := hN.2.1 e₁ he₁ hs₁
  have hr₁ : e₁.kind.isRandom = true := by revert hs₁; cases e₁.kind <;> simp [Kind.isSolid, Kind.isRandom]
  have hxR : (liftA 1 x).isRight = true := by simpa using hx
  obtain ⟨n1, l1, k1, a1, w1, x1, s1, r1, o1⟩ := rxC_facts hx hs₁ hx₁ hne₁ (hK₀ e₁ he₁ hr₁)
  have hxL : x.isLeft = false := by cases x <;> simp_all
  have f0 : NewOK c₀ ∧ c₀.label = none ∧ c₀.x.isRight = true ∧ c₀.kind.isSolid = true ∧
      atB (newA 0) c₀ = true ∧ (isNewA n c₀.x || isNewA n c₀.y) = true ∧
      (c₀.x.isLeft || c₀.y.isLeft) = false ∧ c₀.kind.ord = 1 := by
    rcases hc₀ with rfl | rfl
    · exact ⟨NewOK_G _ (by simp), rfl, hxR, rfl, by simp [atB, mkC], by simp [mkC],
        by simp [mkC, hxL], rfl⟩
    · exact ⟨NewOK_G _ (by simp), rfl, rfl, rfl, by simp [atB, mkC], by simp [mkC],
        by simp [mkC, hxL], rfl⟩
  obtain ⟨n0, l0, k0, s0, a0, w0, x0, o0⟩ := f0
  have w3 : (mkC (.waved .s) (liftA 1 x) (newA 0) : Comp (Atom k (n + 1))).kind.isSolid = false :=
    rfl
  have h1 : e₁.kind.ord = 1 := by
    obtain ⟨ch, h⟩ : ∃ ch, e₁.kind = .G ch := by revert hs₁; cases e₁.kind <;> simp [Kind.isSolid]
    rw [h]; rfl
  refine termOK_mk (K := K) (R := [e₁]) lab
    [mkC (.waved .s) (liftA 1 x) (newA 0), c₀, rxC x e₁] [] co 1 hKR (by simp [hr₁])
    (by simpa using hcs) (by simp) ?_ ?_ ?_ ?_ (fun _ _ => false) (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨NewOK_waved _ _ _, rfl⟩
    · exact ⟨n0, l0⟩
    · exact ⟨n1, l1⟩
  · intro c hc hr
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · simp [mkC, Kind.isRandom] at hr
    · exact k0
    · exact k1
  · have : (Kind.waved Wave.s).ord = 2 := rfl
    simp only [List.append_nil, ordL_cons, ordL_nil, o0, o1, h1, mkC, this]
    norm_num
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [List.append_nil, List.filter_cons, List.filter_nil, s0, s1, a0, a1, w3,
      Bool.and_true, Bool.false_and, Bool.false_eq_true, ite_false, ite_true, List.length_cons,
      List.length_nil]
    omega
  · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | h | rfl
    · simp [mkC, Kind.isSolid]
    · rw [h]; revert w0; cases isNewA n c₀.x <;> cases isNewA n c₀.y <;> simp
    · revert w1; cases isNewA n (rxC x e₁).x <;> cases isNewA n (rxC x e₁).y <;> simp
  · simp only [List.append_nil, List.filter_cons, List.filter_nil, s0, s1, w3, Bool.false_eq_true,
      ite_false, ite_true, List.length_cons, List.length_nil]
    norm_num
  · intro h; simp at h
  · simp only [List.append_nil, List.filter_cons, List.filter_nil, s0, s1, x0, x1, w3, hs₁,
      Bool.true_and, Bool.false_and, Bool.false_eq_true, ite_false]
    split_ifs <;> simp
  · intro _ h; simp at h
  · intro hl
    refine ⟨labF lab (rxC x e₁), hcs.mem_iff.2 ?_, by rw [labF_kind]; exact r1⟩
    simp only [labW_eq_map]
    exact List.mem_map_of_mem (by simp)
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    refine sameMol_of_waved (w := .s) (hcs.mem_iff.2 ?_) hxR rfl
    simp only [labW_eq_map]
    refine List.mem_map.2 ⟨mkC (.waved .s) (liftA 1 x) (newA 0), by simp, ?_⟩
    exact labF_nonrandom lab rfl

/-- The term `m ∑_α s_{xα}(G_{αα} - m) 𝒢`, without or with the label `Q_x`. -/
private theorem termL3 {Γ : Graph k n} {x : Atom k n} (hx : x.isRight = true)
    (lab : Option (Atom k (n + 1))) (hlab : lab = none ∨ lab = some (liftA 1 x)) (co : Coeff) :
    TermOK Γ x (t1 (labW lab (liftCs 1 Γ.comps ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.light .plus) (newA 0) (newA 0)])) co) := by
  have hxR : (liftA 1 x).isRight = true := by simpa using hx
  refine termOK_mk (K := Γ.comps) (R := []) lab [mkC (.waved .s) (liftA 1 x) (newA 0),
    mkC (.light .plus) (newA 0) (newA 0)] [] co 1 (by simp) (by simp) (by simp) (by simp) ?_ ?_
    (by simp [ordL, mkC, Kind.ord]) (fun i => by simp [mkC, Kind.isSolid])
    (fun _ _ => false) (by simp) (by simp [mkC, Kind.isSolid]) (by simp [mkC, Kind.isSolid])
    (by simp [mkC, Kind.isSolid]) (by simp [mkC, Kind.isSolid]) (fun _ h => by simp at h) ?_ ?_
  · intro c hc
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨NewOK_waved _ _ _, rfl⟩
    · exact ⟨NewOK_light _ _, rfl⟩
  · intro c hc hr
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp_all [mkC, Kind.isRandom]
  · intro hl
    refine ⟨labF lab (mkC (.light .plus) (newA 0) (newA 0)), ?_, by rw [labF_kind]; rfl⟩
    simp only [labW_eq_map]
    exact List.mem_map_of_mem (by simp)
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    refine sameMol_of_waved (w := .s) ?_ hxR rfl
    simp only [labW_eq_map]
    refine List.mem_map.2 ⟨mkC (.waved .s) (liftA 1 x) (newA 0), by simp, ?_⟩
    exact labF_nonrandom lab rfl

/-- The derivative terms of the multi-edge expansion, case (i): `∂_{h_{αx}}` of a random
component `c` of `f` not attached to `x`, without or with the label `Q_x`. -/
private theorem termDs {C : ℕ} {Γ : Graph k n} {x : Atom k n} {P F : List (Comp (Atom k n))}
    {e₁ : Comp (Atom k n)} (hN : Γ.Normal C) (hK₀ : Γ.RandomFirstInt) (hx : x.isRight = true)
    (hKR : Γ.comps.Perm (P ++ F ++ [e₁])) (he₁ : e₁ ∈ Γ.comps) (hs₁ : e₁.kind.isSolid = true)
    (hx₁ : e₁.x = x ∨ e₁.y = x)
    (hF : ∀ c ∈ F, c.kind.isRandom = true → c.x ≠ x ∧ c.endB ≠ x ∧ c.x.isRight = true ∧
      (c.kind.isSolid = true → c.endB = c.y) ∧ (c.kind.isSolid = false → c.endB = c.x))
    (o : Bool) {d : List (Comp (Atom k (n + 1)))}
    (hd : d ∈ dTerms (if o then newA 0 else liftA 1 x) (if o then liftA 1 x else newA 0)
      (liftCs 1 F))
    (lab : Option (Atom k (n + 1))) (hlab : lab = none ∨ lab = some (liftA 1 x)) (co : Coeff) :
    TermOK Γ x (t1 (labW lab (liftCs 1 P ++ d ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      rxC x e₁])) co) := by
  obtain ⟨c₀, K₀, ps, hF', hc₀, hps, rfl⟩ := dTerms_lift_split hd
  have hpm := dPieces_lift hps
  have hr₀ : c₀.kind.isRandom = true := by
    rcases hpm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact (kind_ord_of_pm h).2.2
  obtain ⟨cx, cb, cxR, hbS, hbW⟩ := hF c₀ hc₀ hr₀
  have hne₁ := hN.2.1 e₁ he₁ hs₁
  have hr₁ : e₁.kind.isRandom = true := by revert hs₁; cases e₁.kind <;> simp [Kind.isSolid, Kind.isRandom]
  have hxR : (liftA 1 x).isRight = true := by simpa using hx
  obtain ⟨n1, l1, k1, a1, w1, x1, s1, r1, o1⟩ := rxC_facts hx hs₁ hx₁ hne₁ (hK₀ e₁ he₁ hr₁)
  have hxL : x.isLeft = false := by cases x <;> simp_all
  have hcL : c₀.x.isLeft = false := by cases h : c₀.x <;> simp_all
  have hord : c₀.kind.ord = 1 ∨ c₀.kind.ord = 0 := by
    rcases hpm with ⟨h, -⟩ | ⟨h, -⟩
    · rcases h with h | h | h <;> exact (kind_ord_of_pm (ch := .plus) (by simp [h])).1
    · rcases h with h | h | h <;> exact (kind_ord_of_pm (ch := .minus) (by simp [h])).1
  have hK : Γ.comps.Perm ((P ++ K₀) ++ [e₁, c₀]) := by
    refine hKR.trans ?_
    simp only [List.append_assoc]
    refine List.Perm.append_left P ?_
    refine (hF'.append_right [e₁]).trans ?_
    simp only [List.append_assoc]
    exact List.Perm.append_left K₀ (List.perm_append_comm (l₁ := [c₀]) (l₂ := [e₁]))
  -- the two factors: one at `α`, one between `x` and an old atom
  have hpm' : ∃ ch, ps = [mkC (.G ch) (liftA 1 c₀.x) (newA 0), mkC (.G ch) (liftA 1 x)
        (liftA 1 c₀.endB)] ∨
      ps = [mkC (.G ch) (liftA 1 c₀.x) (liftA 1 x), mkC (.G ch) (newA 0) (liftA 1 c₀.endB)] := by
    cases o
    · rcases hpm with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · refine ⟨.plus, Or.inr ?_⟩
        simp only [Bool.false_eq_true, ite_false]
        rw [solidC_of_ne (by simpa using cx), solidC_of_ne (by simp)]
      · refine ⟨.minus, Or.inl ?_⟩
        simp only [Bool.false_eq_true, ite_false]
        rw [solidC_of_ne (by simp), solidC_of_ne (by simpa using cb.symm)]
    · rcases hpm with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · refine ⟨.plus, Or.inl ?_⟩
        simp only [ite_true]
        rw [solidC_of_ne (by simp), solidC_of_ne (by simpa using cb.symm)]
      · refine ⟨.minus, Or.inr ?_⟩
        simp only [ite_true]
        rw [solidC_of_ne (by simpa using cx), solidC_of_ne (by simp)]
  obtain ⟨ch, hps'⟩ := hpm'
  have hs1 : 1 ≤ (2 - c₀.kind.ord).toNat := by rcases hord with h | h <;> simp [h]
  have w3 : (mkC (.waved .s) (liftA 1 x) (newA 0) : Comp (Atom k (n + 1))).kind.isSolid = false :=
    rfl
  have h1 : e₁.kind.ord = 1 := by
    obtain ⟨ch, h⟩ : ∃ ch, e₁.kind = .G ch := by revert hs₁; cases e₁.kind <;> simp [Kind.isSolid]
    rw [h]; rfl
  refine termOK_mk (K := P ++ K₀) (R := [e₁, c₀]) lab
    (ps ++ [mkC (.waved .s) (liftA 1 x) (newA 0), rxC x e₁]) [] co (2 - c₀.kind.ord).toNat hK
    (by simp [hr₁, hr₀]) (List.Perm.of_eq (by simp [liftCs, List.append_assoc]))
    (by simp) ?_ ?_ ?_ ?_ (fun _ _ => false) (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | rfl | rfl
    · exact ⟨dPieces_newOK hps c hc, by
        rcases hps' with rfl | rfl <;>
          (simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
           rcases hc with rfl | rfl <;> rfl)⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
    · exact ⟨n1, l1⟩
  · intro c hc hr
    simp only [List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | rfl | rfl
    · rcases hps' with rfl | rfl <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
         rcases hc with rfl | rfl <;> simp [mkC, cxR, hx])
    · simp [mkC, Kind.isRandom] at hr
    · exact k1
  · have e2 : (Kind.G ch).ord = 1 := rfl
    have e3 : (Kind.waved Wave.s).ord = 2 := rfl
    rcases hps' with rfl | rfl <;>
      (simp only [List.append_nil, ordL_append, ordL_cons, ordL_nil, o1, h1, mkC, e2, e3]
       rcases hord with h | h <;> rw [h] <;> norm_num)
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rcases hps' with rfl | rfl <;>
      (simp only [List.append_nil, List.cons_append, List.nil_append, List.filter_cons,
        List.filter_nil, s1, a1, w3, Bool.and_true, Bool.false_and, Bool.false_eq_true, ite_false,
        ite_true]
       simp [mkC, Kind.isSolid, atB])
  · rcases hps' with rfl | rfl <;>
      (simp only [List.append_nil, List.cons_append, List.nil_append, List.filter_cons,
        List.filter_nil, s1, w3, Bool.false_and, Bool.false_eq_true, ite_false]
       have : (isNewA n (rxC x e₁).x || isNewA n (rxC x e₁).y) = true := w1
       revert this
       cases isNewA n (rxC x e₁).x <;> cases isNewA n (rxC x e₁).y <;>
         simp [mkC, Kind.isSolid] <;> omega)
  · rcases hps' with rfl | rfl <;>
      (simp only [List.append_nil, List.cons_append, List.nil_append, List.filter_cons,
        List.filter_nil, s1, w3, Bool.false_eq_true, ite_false]
       simp [mkC, Kind.isSolid])
  · intro h; omega
  · have hcS : (c₀.kind.isSolid && (c₀.x.isLeft || c₀.y.isLeft)) =
        (c₀.endB.isLeft && c₀.kind.isSolid) := by
      by_cases hs : c₀.kind.isSolid = true
      · simp [hs, hcL, hbS hs]
      · have hs' : c₀.kind.isSolid = false := by simpa using hs
        simp [hs']
    have hbL : c₀.kind.isSolid = false → c₀.endB.isLeft = false := fun hs => by rw [hbW hs]; exact hcL
    rcases hps' with rfl | rfl <;>
      (simp only [List.append_nil, List.cons_append, List.nil_append, List.filter_cons,
        List.filter_nil, s1, x1, w3, hs₁, hcS, Bool.true_and, Bool.false_and, Bool.false_eq_true,
        ite_false]
       by_cases hs : c₀.kind.isSolid = true
       · simp only [hs, Bool.and_true]
         simp [mkC, Kind.isSolid, hxL, hcL]
         split_ifs <;> simp
       · have hb := hbL (by simpa using hs)
         have hs' : c₀.kind.isSolid = false := by simpa using hs
         simp only [hs', Bool.and_false]
         simp [mkC, Kind.isSolid, hxL, hcL, hb]
         try (split_ifs <;> simp))
  · intro _ h; omega
  · intro hl
    refine ⟨labF lab (rxC x e₁), ?_, by rw [labF_kind]; exact r1⟩
    simp only [labW_eq_map]
    exact List.mem_map_of_mem (by simp)
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    refine sameMol_of_waved (w := .s) ?_ hxR rfl
    simp only [labW_eq_map]
    refine List.mem_map.2 ⟨mkC (.waved .s) (liftA 1 x) (newA 0), by simp, ?_⟩
    exact labF_nonrandom lab rfl

/-- The new atom `α` of a main term of the `GḠ` expansion is standard neutral. -/
private theorem std_alpha {K : List (Comp (Atom k n))} {x a b : Atom k n} (o : Bool) :
    (⟨liftCs 1 K ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      if o then mkC (.G .plus) (newA 0) (liftA 1 a) else mkC (.G .plus) (liftA 1 a) (newA 0),
      if o then mkC (.G .minus) (newA 0) (liftA 1 b) else mkC (.G .minus) (liftA 1 b) (newA 0)],
      1⟩ : Graph k (n + 1)).stdNeutralAt (newA 0) = true := by
  have hK : (liftCs 1 K).filter (atB (newA 0)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc
    obtain ⟨c₀, -, rfl⟩ := mem_liftCs.1 hc
    simp [atB, Comp.map]
  rw [std_eq]
  simp only [List.filter_append, hK, List.nil_append]
  rw [ends_local]
  simp only [List.filter_append, hK, List.nil_append]
  cases o <;> simp [List.filter_cons, List.filterMap_cons, atB, mkC, Kind.isSolid, endF, stdM,
    matchedEnds]

private theorem edge_at {Γ : Graph k n} {x : Atom k n} {ch : Charge} {out : Bool} {j : ℕ}
    (e₁ : Comp (Atom k n)) (h : j ∈ Γ.edgeIdx x ch out) :
    Γ.comps[j]? = some (Γ.comps.getD j e₁) ∧ (Γ.comps.getD j e₁).kind = .G ch ∧
      (if out = true then (Γ.comps.getD j e₁).x = x ∧ (Γ.comps.getD j e₁).y ≠ x
        else (Γ.comps.getD j e₁).y = x ∧ (Γ.comps.getD j e₁).x ≠ x) := by
  obtain ⟨c, hc, hk, ho⟩ := mem_edgeIdx.1 h
  have : Γ.comps.getD j e₁ = c := by simp [List.getD_eq_getElem?_getD, hc]
  rw [this]
  exact ⟨hc, hk, ho⟩

end MEBase

section LengthsME

variable {k n : ℕ}

private theorem len_oOut (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ) (e₁ : Comp (Atom k n)) :
    (oOut x Γ i₁ is₂ e₁).length ≤ 10 * Γ.comps.length + 10 := by
  have h1 := len_edgeIdx Γ x .minus true
  have h2 := len_edgeIdx Γ x .plus false
  have h3 := len_edgeIdx Γ x .minus false
  have h4 : (oDs x Γ i₁ e₁).length ≤ Γ.comps.length := by
    unfold oDs
    rw [List.length_map]
    refine (len_dTerms _ _ _).trans ?_
    simp only [liftCs, List.length_map]
    exact len_eraseIdxs _ _
  have h5 := len_ite_single (is₂.isEmpty = true) (t1 (oE1 x Γ i₁ e₁) ((is₂.length : Coeff) * cm * Γ.coeff))
  have h6 := len_ite_single (is₂.isEmpty = true)
    (t1 (labelQs (liftA 1 x) (oE1 x Γ i₁ e₁)) (-(is₂.length : Coeff) * cm * Γ.coeff))
  have h7 := len_ite_single ((Γ.edgeIdx x .minus false).length = 0)
    (t1 (oE2 x Γ i₁ e₁) (((Γ.edgeIdx x .minus false).length : Coeff) * cm * Γ.coeff))
  have h8 := len_ite_single ((Γ.edgeIdx x .minus false).length = 0)
    (t1 (labelQs (liftA 1 x) (oE2 x Γ i₁ e₁))
      (-((Γ.edgeIdx x .minus false).length : Coeff) * cm * Γ.coeff))
  unfold oOut
  simp only [List.length_append, List.length_map, List.length_singleton]
  omega

private theorem len_iOut (x : Atom k n) (Γ : Graph k n) (i₁ : ℕ) (is₂ : List ℕ) (e₁ : Comp (Atom k n)) :
    (iOut x Γ i₁ is₂ e₁).length ≤ 10 * Γ.comps.length + 10 := by
  have h3 := len_edgeIdx Γ x .minus false
  have h4 : (iDs x Γ i₁ e₁).length ≤ Γ.comps.length := by
    unfold iDs
    rw [List.length_map]
    refine (len_dTerms _ _ _).trans ?_
    simp only [liftCs, List.length_map]
    exact len_eraseIdxs _ _
  have h5 := len_ite_single (is₂.isEmpty = true) (t1 (iE1 x Γ i₁ e₁) ((is₂.length : Coeff) * cm * Γ.coeff))
  have h6 := len_ite_single (is₂.isEmpty = true)
    (t1 (labelQs (liftA 1 x) (iE1 x Γ i₁ e₁)) (-(is₂.length : Coeff) * cm * Γ.coeff))
  unfold iOut
  simp only [List.length_append, List.length_map, List.length_singleton]
  omega

end LengthsME

/-! ## The terms of the multi-edge expansion -/

section METerms

variable {k n : ℕ}

/-- The hypotheses of the multi-edge expansion at `x` used for its terms. -/
structure MEHyp (C : ℕ) (x : Atom k n) (Γ : Graph k n) : Prop where
  normal : Γ.Normal C
  plain : Γ.Plain
  lf : Γ.LabelFree
  K0 : Γ.RandomFirstInt
  right : x.isRight = true
  wt0 : Γ.wt x = 0
  HM : 3 ≤ Γ.deg x ∨ (Γ.stdNeutralAt x = false ∧ ∀ y y', ¬ Γ.GGInputAt x y y')

variable {C : ℕ} {x : Atom k n} {Γ : Graph k n}

/-- The random components outside the solid edges at `x` are not attached to `x`. -/
private theorem MEHyp.fL_facts {xIdx : List ℕ} (H : MEHyp C x Γ)
    (hxIdx : ∀ c ∈ eraseIdxs xIdx Γ.comps, ∀ ch, c.kind = .G ch → c.x ≠ x ∧ c.y ≠ x) :
    ∀ c ∈ eraseIdxs xIdx Γ.comps, c.kind.isRandom = true → c.x ≠ x ∧ c.endB ≠ x ∧
      c.x.isRight = true ∧ (c.kind.isSolid = true → c.endB = c.y) ∧
      (c.kind.isSolid = false → c.endB = c.x) := by
  intro c hc hr
  have hcm : c ∈ Γ.comps := mem_eraseIdxs_of_mem hc
  obtain ⟨-, p2, p3, -, -⟩ := H.plain c hcm
  have hk : (∃ ch, c.kind = .G ch) ∨ (∃ ch, c.kind = .weight ch) ∨ (∃ ch, c.kind = .light ch) := by
    revert hr p2 p3; cases c.kind <;> simp [Kind.isRandom]
  have hxr := H.K0 c hcm hr
  rcases hk with ⟨ch, hch⟩ | hw
  · obtain ⟨h1, h2⟩ := hxIdx c hc ch hch
    refine ⟨h1, ?_, hxr, fun _ => ?_, fun h => by simp [hch, Kind.isSolid] at h⟩
    · simp [Comp.endB, hch, Kind.isWeight, h2]
    · simp [Comp.endB, hch, Kind.isWeight]
  · have hx : c.x ≠ x := wt_zero_imp H.wt0 hcm hw
    have hW : c.kind.isWeight = true := by rcases hw with ⟨ch, h⟩ | ⟨ch, h⟩ <;> simp [h, Kind.isWeight]
    have hS : c.kind.isSolid = false := by rcases hw with ⟨ch, h⟩ | ⟨ch, h⟩ <;> simp [h, Kind.isSolid]
    refine ⟨hx, by simp [Comp.endB, hW, hx], hxr, ?_, fun _ => by simp [Comp.endB, hW]⟩
    intro h
    rw [hS] at h
    cases h

/-- The main terms of case (i) of the multi-edge expansion. -/
private theorem MEHyp.baseOut (H : MEHyp C x Γ) {i₁ : ℕ} {is₂ : List ℕ} {e₁ : Comp (Atom k n)}
    (Ctx : OutCtxS C x Γ i₁ is₂ e₁) (ch : Charge) (out : Bool) (j : ℕ)
    (hj : j ∈ Γ.edgeIdx x ch out) (hcho : (ch = .minus ∧ out = true) ∨ (ch = .plus ∧ out = false))
    (lab : Option (Atom k (n + 1))) (extra : List (Comp (Atom k (n + 1))))
    (hex : (extra = [] ∧ lab = none) ∨ (∃ ch, extra = [mkC (.light ch) (liftA 1 x) (liftA 1 x)] ∧
      lab = none) ∨ (∃ ch, extra = [mkC (.weight ch) (liftA 1 x) (liftA 1 x)] ∧
      lab = some (liftA 1 x))) (co : Coeff) :
    TermOK Γ x (t1 (labW lab (liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++ ([oSx x, rxC x e₁,
      rxC x (Γ.comps.getD j e₁)] ++ extra))) co) := by
  obtain ⟨hk₁, hx₁, hy₁⟩ := Ctx.e₁spec
  have he₁ := Ctx.e₁mem
  obtain ⟨hjc, hkj, hoj⟩ := edge_at e₁ hj
  set ej := Γ.comps.getD j e₁ with hej
  have hij : i₁ ≠ j := by
    intro h
    subst h
    have hi : i₁ ∈ Γ.edgeIdx x .plus true := by rw [Ctx.hOP]; exact List.mem_cons_self ..
    rcases hcho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact edgeIdx_disjoint (Or.inl (by simp)) hi hj
    · exact edgeIdx_disjoint (Or.inr (by simp)) hi hj
  have hperm := (eraseIdxs_two_perm hij Ctx.hL hjc).symm
  have hej_mem : ej ∈ Γ.comps := List.mem_of_getElem? hjc
  have hsj : ej.kind.isSolid = true := by rw [hkj]; rfl
  have hxj : ej.x = x ∨ ej.y = x := by
    cases out
    · have h : ej.y = x ∧ ej.x ≠ x := by simpa using hoj
      exact Or.inr h.1
    · have h : ej.x = x ∧ ej.y ≠ x := by simpa using hoj
      exact Or.inl h.1
  refine termBase H.normal H.K0 H.right hperm he₁ hej_mem (by simp [hk₁, Kind.isSolid]) hsj
    (Or.inl hx₁) hxj lab extra hex ?_ co
  rcases H.HM with h3 | ⟨hstd, hgg⟩
  · exact Or.inl h3
  · by_cases h3 : 3 ≤ Γ.deg x
    · exact Or.inl h3
    rcases hcho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine Or.inr ⟨hstd, ?_⟩
      have h1 : rxC x e₁ = mkC (.G .plus) (newA 0) (liftA 1 e₁.y) := by rw [rxC_of_x hx₁ hy₁, hk₁]
      have h2 : rxC x ej = mkC (.G .minus) (newA 0) (liftA 1 ej.y) := by
        simp only [ite_true] at hoj
        rw [rxC_of_x hoj.1 hoj.2, hkj]
      rw [h1, h2]
      exact std_alpha (K := eraseIdxs [i₁, j] Γ.comps) (x := x) (a := e₁.y) (b := ej.y) true
    · exfalso
      simp only [Bool.false_eq_true, ite_false] at hoj
      have hsum := deg_eq_sum H.normal x
      have l1 : 1 ≤ (Γ.edgeIdx x .plus true).length := by rw [Ctx.hOP]; simp
      have l2 : 1 ≤ (Γ.edgeIdx x .plus false).length := List.length_pos_of_mem hj
      have hd2 : Γ.deg x = 2 := by omega
      exact hgg e₁.y ej.x ⟨hd2, .plus, ⟨e₁, he₁, hk₁, hx₁, rfl⟩, ⟨ej, hej_mem, hkj, rfl, hoj.1⟩⟩

/-- The terms of case (i) of the multi-edge expansion. -/
private theorem MEHyp.outTerms (H : MEHyp C x Γ) {i₁ : ℕ} {is₂ : List ℕ} {e₁ : Comp (Atom k n)}
    (Ctx : OutCtxS C x Γ i₁ is₂ e₁) : ∀ T ∈ oOut x Γ i₁ is₂ e₁, TermOK Γ x T := by
  intro T hT
  unfold oOut at hT
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  obtain ⟨hk₁, hx₁, hy₁⟩ := Ctx.e₁spec
  have he₁ := Ctx.e₁mem
  have hs₁ : e₁.kind.isSolid = true := by simp [hk₁, Kind.isSolid]
  have hrx : oGy e₁ = rxC x e₁ := by rw [rxC_of_x hx₁ hy₁, hk₁]; rfl
  have hBM : ∀ j ∈ Γ.edgeIdx x .minus true, oBaseM x Γ i₁ e₁ j =
      liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++ ([oSx x, rxC x e₁, rxC x (Γ.comps.getD j e₁)] ++ []) := by
    intro j hj
    obtain ⟨-, hkj, hoj⟩ := edge_at e₁ hj
    simp only [ite_true] at hoj
    rw [rxC_of_x hoj.1 hoj.2, hkj, ← hrx]
    rfl
  have hBP : ∀ j ∈ Γ.edgeIdx x .plus false, oBaseP x Γ i₁ e₁ j =
      liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++ ([oSx x, rxC x e₁, rxC x (Γ.comps.getD j e₁)] ++ []) := by
    intro j hj
    obtain ⟨-, hkj, hoj⟩ := edge_at e₁ hj
    simp only [Bool.false_eq_true, ite_false] at hoj
    rw [rxC_of_y hoj.1 hoj.2, hkj, ← hrx]
    rfl
  have hE : Γ.comps.Perm (Γ.comps.eraseIdx i₁ ++ [e₁]) := (eraseIdx_perm Ctx.hL).symm
  have hDs : Γ.comps.Perm (pickIdxs ((oXIdx x Γ).filter (· != i₁)) Γ.comps ++
      eraseIdxs (oXIdx x Γ) Γ.comps ++ [e₁]) := (xe_fL_perm Ctx).symm
  have hF := H.fL_facts (xIdx := oXIdx x Γ) (fun c hc ch hk => fL_untouched H.normal hc hk)
  have hDs' : ∀ d ∈ oDs x Γ i₁ e₁, ∃ d₀ ∈ dTerms (if true = true then newA 0 else liftA 1 x)
      (if true = true then liftA 1 x else newA 0) (liftCs 1 (eraseIdxs (oXIdx x Γ) Γ.comps)),
      d = liftCs 1 (pickIdxs ((oXIdx x Γ).filter (· != i₁)) Γ.comps) ++ d₀ ++
        [mkC (.waved .s) (liftA 1 x) (newA 0), rxC x e₁] := by
    intro d hd
    unfold oDs at hd
    obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
    exact ⟨d₀, by simpa using hd₀, by rw [← hrx]; rfl⟩
  rcases hT with (((((((((((((⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) |
    rfl) | h) | h) | ⟨d, hd, rfl⟩) | rfl) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | rfl) | h) | h) |
    ⟨d, hd, rfl⟩
  · rw [hBM j hj]
    exact H.baseOut Ctx .minus true j hj (Or.inl ⟨rfl, rfl⟩) none [] (Or.inl ⟨rfl, rfl⟩) _
  · rw [hBP j hj]
    exact H.baseOut Ctx .plus false j hj (Or.inr ⟨rfl, rfl⟩) none [] (Or.inl ⟨rfl, rfl⟩) _
  · rw [hBM j hj, List.append_assoc, List.append_nil]
    exact H.baseOut Ctx .minus true j hj (Or.inl ⟨rfl, rfl⟩) none _
      (Or.inr (Or.inl ⟨_, rfl, rfl⟩)) _
  · rw [hBP j hj, List.append_assoc, List.append_nil]
    exact H.baseOut Ctx .plus false j hj (Or.inr ⟨rfl, rfl⟩) none _
      (Or.inr (Or.inl ⟨_, rfl, rfl⟩)) _
  · exact termL3 H.right none (Or.inl rfl) _
  · split_ifs at h
    · simp at h
    · rw [List.mem_singleton] at h
      subst h
      exact termE1 H.normal H.K0 H.right hE he₁ hs₁ (Or.inl hx₁) _ .plus (Or.inl rfl) none
        (Or.inl rfl) _ (List.Perm.of_eq (by simp [oE1, oSx, labW, hrx])) _
  · split_ifs at h
    · simp at h
    · rw [List.mem_singleton] at h
      subst h
      exact termE1 H.normal H.K0 H.right hE he₁ hs₁ (Or.inl hx₁) _ .minus (Or.inr rfl) none
        (Or.inl rfl) _ (List.Perm.of_eq (by simp [oE2, oSx, labW, hrx])) _
  · obtain ⟨d₀, hd₀, rfl⟩ := hDs' d hd
    exact termDs H.normal H.K0 H.right hDs he₁ hs₁ (Or.inl hx₁) hF true hd₀ none (Or.inl rfl) _
  · exact termQx H.right ⟨e₁, he₁, by simp [hk₁, Kind.isRandom]⟩ _
  · rw [hBM j hj, List.append_assoc, List.append_nil]
    exact H.baseOut Ctx .minus true j hj (Or.inl ⟨rfl, rfl⟩) (some (liftA 1 x)) _
      (Or.inr (Or.inr ⟨_, rfl, rfl⟩)) _
  · rw [hBP j hj, List.append_assoc, List.append_nil]
    exact H.baseOut Ctx .plus false j hj (Or.inr ⟨rfl, rfl⟩) (some (liftA 1 x)) _
      (Or.inr (Or.inr ⟨_, rfl, rfl⟩)) _
  · exact termL3 H.right (some (liftA 1 x)) (Or.inr rfl) _
  · split_ifs at h
    · simp at h
    · rw [List.mem_singleton] at h
      subst h
      exact termE1 H.normal H.K0 H.right hE he₁ hs₁ (Or.inl hx₁) _ .plus (Or.inl rfl)
        (some (liftA 1 x)) (Or.inr rfl) _ (List.Perm.of_eq (by simp [oE1, oSx, labW, hrx])) _
  · split_ifs at h
    · simp at h
    · rw [List.mem_singleton] at h
      subst h
      exact termE1 H.normal H.K0 H.right hE he₁ hs₁ (Or.inl hx₁) _ .minus (Or.inr rfl)
        (some (liftA 1 x)) (Or.inr rfl) _ (List.Perm.of_eq (by simp [oE2, oSx, labW, hrx])) _
  · obtain ⟨d₀, hd₀, rfl⟩ := hDs' d hd
    exact termDs H.normal H.K0 H.right hDs he₁ hs₁ (Or.inl hx₁) hF true hd₀ (some (liftA 1 x))
      (Or.inr rfl) _

/-- The terms of case (iii) of the multi-edge expansion. -/
private theorem MEHyp.inTerms (H : MEHyp C x Γ) {i₁ : ℕ} {is₂ : List ℕ} {e₁ : Comp (Atom k n)}
    (Ctx : InCtxS C x Γ i₁ is₂ e₁) : ∀ T ∈ iOut x Γ i₁ is₂ e₁, TermOK Γ x T := by
  intro T hT
  unfold iOut at hT
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  obtain ⟨hk₁, hx₁, hy₁⟩ := Ctx.e₁spec
  have he₁ := Ctx.e₁mem
  have hs₁ : e₁.kind.isSolid = true := by simp [hk₁, Kind.isSolid]
  have hrx : iGw e₁ = rxC x e₁ := by rw [rxC_of_y hx₁ hy₁, hk₁]; rfl
  have hbase : ∀ j ∈ Γ.edgeIdx x .minus false, ∀ (lab : Option (Atom k (n + 1)))
      (extra : List (Comp (Atom k (n + 1)))),
      ((extra = [] ∧ lab = none) ∨ (∃ ch, extra = [mkC (.light ch) (liftA 1 x) (liftA 1 x)] ∧
        lab = none) ∨ (∃ ch, extra = [mkC (.weight ch) (liftA 1 x) (liftA 1 x)] ∧
        lab = some (liftA 1 x))) → ∀ co,
      TermOK Γ x (t1 (labW lab (iBaseM x Γ i₁ e₁ j ++ extra)) co) := by
    intro j hj lab extra hex co
    obtain ⟨hjc, hkj, hoj⟩ := edge_at e₁ hj
    simp only [Bool.false_eq_true, ite_false] at hoj
    set ej := Γ.comps.getD j e₁ with hej
    have hij : i₁ ≠ j := by
      intro h
      subst h
      have hi : i₁ ∈ Γ.edgeIdx x .plus false := by rw [Ctx.hIP]; exact List.mem_cons_self ..
      exact edgeIdx_disjoint (Or.inl (by simp)) hi hj
    have hperm := (eraseIdxs_two_perm hij Ctx.hL hjc).symm
    have hej_mem : ej ∈ Γ.comps := List.mem_of_getElem? hjc
    have hsj : ej.kind.isSolid = true := by rw [hkj]; rfl
    have hb : iBaseM x Γ i₁ e₁ j ++ extra =
        liftCs 1 (eraseIdxs [i₁, j] Γ.comps) ++ ([oSx x, rxC x e₁, rxC x ej] ++ extra) := by
      rw [rxC_of_y hoj.1 hoj.2, hkj, ← hrx]
      unfold iBaseM
      simp only [List.append_assoc]
      rfl
    rw [hb]
    refine termBase H.normal H.K0 H.right hperm he₁ hej_mem hs₁ hsj (Or.inr hx₁) (Or.inr hoj.1)
      lab extra hex ?_ co
    rcases H.HM with h3 | ⟨hstd, -⟩
    · exact Or.inl h3
    · by_cases h3 : 3 ≤ Γ.deg x
      · exact Or.inl h3
      refine Or.inr ⟨hstd, ?_⟩
      have h1 : rxC x e₁ = mkC (.G .plus) (liftA 1 e₁.x) (newA 0) := by rw [rxC_of_y hx₁ hy₁, hk₁]
      have h2 : rxC x ej = mkC (.G .minus) (liftA 1 ej.x) (newA 0) := by
        rw [rxC_of_y hoj.1 hoj.2, hkj]
      rw [h1, h2]
      exact std_alpha (K := eraseIdxs [i₁, j] Γ.comps) (x := x) (a := e₁.x) (b := ej.x) false
  have hE : Γ.comps.Perm (Γ.comps.eraseIdx i₁ ++ [e₁]) := (eraseIdx_perm Ctx.hL).symm
  have hDs : Γ.comps.Perm (pickIdxs ((iXIdx x Γ).filter (· != i₁)) Γ.comps ++
      eraseIdxs (iXIdx x Γ) Γ.comps ++ [e₁]) := (ixe_fL_perm Ctx).symm
  have hF := H.fL_facts (xIdx := iXIdx x Γ) (fun c hc ch hk => fL_untouched_in Ctx hc hk)
  have hDs' : ∀ d ∈ iDs x Γ i₁ e₁, ∃ d₀ ∈ dTerms (if false = true then newA 0 else liftA 1 x)
      (if false = true then liftA 1 x else newA 0) (liftCs 1 (eraseIdxs (iXIdx x Γ) Γ.comps)),
      d = liftCs 1 (pickIdxs ((iXIdx x Γ).filter (· != i₁)) Γ.comps) ++ d₀ ++
        [mkC (.waved .s) (liftA 1 x) (newA 0), rxC x e₁] := by
    intro d hd
    unfold iDs at hd
    obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 hd
    exact ⟨d₀, by simpa using hd₀, by rw [← hrx]; rfl⟩
  have hE1 : ∀ (lab : Option (Atom k (n + 1))), (lab = none ∨ lab = some (liftA 1 x)) → ∀ co,
      TermOK Γ x (t1 (labW lab (iE1 x Γ i₁ e₁)) co) := by
    intro lab hlab co
    refine termE1 H.normal H.K0 H.right hE he₁ hs₁ (Or.inr hx₁) _ .plus (Or.inr rfl) lab hlab _
      ?_ co
    simp only [iE1, oSx, hrx, labW_eq_map, List.map_append]
    refine List.Perm.append_left _ (List.Perm.map _ ?_)
    exact List.Perm.cons _ (List.Perm.swap _ _ _)
  rcases hT with ((((((((⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | rfl) | h) | ⟨d, hd, rfl⟩) | rfl) |
    ⟨j, hj, rfl⟩) | rfl) | h) | ⟨d, hd, rfl⟩
  · simpa only [labW, List.append_nil] using hbase j hj none [] (Or.inl ⟨rfl, rfl⟩) _
  · exact hbase j hj none _ (Or.inr (Or.inl ⟨_, rfl, rfl⟩)) _
  · exact termL3 H.right none (Or.inl rfl) _
  · split_ifs at h
    · simp at h
    · rw [List.mem_singleton] at h
      subst h
      exact hE1 none (Or.inl rfl) _
  · obtain ⟨d₀, hd₀, rfl⟩ := hDs' d hd
    exact termDs H.normal H.K0 H.right hDs he₁ hs₁ (Or.inr hx₁) hF false hd₀ none (Or.inl rfl) _
  · exact termQx H.right ⟨e₁, he₁, by simp [hk₁, Kind.isRandom]⟩ _
  · exact hbase j hj (some (liftA 1 x)) _ (Or.inr (Or.inr ⟨_, rfl, rfl⟩)) _
  · exact termL3 H.right (some (liftA 1 x)) (Or.inr rfl) _
  · split_ifs at h
    · simp at h
    · rw [List.mem_singleton] at h
      subst h
      exact hE1 (some (liftA 1 x)) (Or.inr rfl) _
  · obtain ⟨d₀, hd₀, rfl⟩ := hDs' d hd
    exact termDs H.normal H.K0 H.right hDs he₁ hs₁ (Or.inr hx₁) hF false hd₀ (some (liftA 1 x))
      (Or.inr rfl) _

private theorem Graph.conj_ggInput {Γ : Graph k n} {x y y' : Atom k n} (h : Γ.conj.GGInputAt x y y') :
    Γ.GGInputAt x y y' := by
  obtain ⟨hd, ch, ⟨c, hc, hk, hx, hy⟩, ⟨c', hc', hk', hx', hy'⟩⟩ := h
  obtain ⟨d, hd', rfl⟩ := Graph.mem_conj_comps.1 hc
  obtain ⟨d', hd'', rfl⟩ := Graph.mem_conj_comps.1 hc'
  refine ⟨by rwa [Graph.conj_deg'] at hd, ch.flip, ⟨d, hd', ?_, hx, hy⟩, ⟨d', hd'', ?_, hx', hy'⟩⟩
  · simp only [Comp.conj_kind] at hk
    have := congrArg Kind.conj hk
    rw [Kind.conj_conj] at this
    rw [this]; rfl
  · simp only [Comp.conj_kind] at hk'
    have := congrArg Kind.conj hk'
    rw [Kind.conj_conj] at this
    rw [this]; rfl

private theorem MEHyp.conj (H : MEHyp C x Γ) : MEHyp C x Γ.conj where
  normal := Graph.conj_Normal H.normal
  plain := Graph.conj_Plain H.plain
  lf := Graph.conj_labelFree' H.lf
  K0 := Graph.conj_randomFirstInt H.K0
  right := H.right
  wt0 := by rw [Graph.conj_wt]; exact H.wt0
  HM := by
    rcases H.HM with h | ⟨h1, h2⟩
    · exact Or.inl (by rw [Graph.conj_deg']; exact h)
    · exact Or.inr ⟨by rw [Graph.conj_std]; exact h1, fun y y' h => h2 y y' (Graph.conj_ggInput h)⟩

/-- The multi-edge expansion at `x` is `O_dot` applied to at most `10 · #components + 10` terms of a
local operation. -/
theorem oMultiET_rep (H : MEHyp C x Γ) (hdeg : 1 ≤ Γ.deg x) :
    ∃ E : TExpansion k n, oMultiET x Γ = E.bind (fun _ g => oDotT g) ∧
      (∀ T ∈ E, TermOK Γ x T) ∧ E.length ≤ 10 * Γ.comps.length + 10 := by
  have hsum := deg_eq_sum H.normal x
  have hXout : ∀ Γ' : Graph k n, Γ'.Normal C → Γ'.xdotsAt x (oXIdx x Γ') = true := by
    intro Γ' hN'
    refine xdotsAt_of_normal hN' x _ fun j hj => ?_
    obtain ⟨c, hc, ch, hk, hxy⟩ := mem_oXIdx.1 hj
    exact ⟨c, hc, by simp [hk, Kind.isSolid], by rcases hxy with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]⟩
  have hXin : ∀ Γ' : Graph k n, Γ'.Normal C → Γ'.xdotsAt x (iXIdx x Γ') = true := by
    intro Γ' hN'
    refine xdotsAt_of_normal hN' x _ fun j hj => ?_
    obtain ⟨c, hc, ch, hk, hxy, -⟩ := mem_iXIdx.1 hj
    exact ⟨c, hc, by simp [hk, Kind.isSolid], Or.inr hxy⟩
  have hpl : (!Γ.comps.all Comp.isPlainB) = false := by simp [all_isPlainB H.lf H.plain]
  have hbind : ∀ E : TExpansion k n, multiEHat x Γ = some E → (∀ T ∈ E, TermOK Γ x T) →
      E.length ≤ 10 * Γ.comps.length + 10 →
      ∃ E : TExpansion k n, oMultiET x Γ = E.bind (fun _ g => oDotT g) ∧
        (∀ T ∈ E, TermOK Γ x T) ∧ E.length ≤ 10 * Γ.comps.length + 10 := by
    intro E hE hT hl
    refine ⟨E, ?_, hT, hl⟩
    unfold oMultiET
    rw [ite_eq_right (by simp [hpl]), hE]
  by_cases h1 : Γ.edgeIdx x .plus true = []
  · by_cases h2 : Γ.edgeIdx x .minus true = []
    · by_cases h3 : Γ.edgeIdx x .plus false = []
      · have h4 : Γ.edgeIdx x .minus false ≠ [] := by
          intro h4
          rw [h1, h2, h3, h4] at hsum
          simp at hsum
          omega
        obtain ⟨i₁, is₂, hIP⟩ := List.exists_cons_of_ne_nil h4
        obtain ⟨e₁, hL⟩ := edge_of_idx (x := x) (i := i₁) (ch := .minus) (out := false)
          (by rw [hIP]; exact List.mem_cons_self ..)
        have Ctx := InCtxS.conj_of H.normal H.plain H.right H.lf hIP hL h1 h2
        have hX' : Γ.conj.xdotsAt x (iXIdx x Γ.conj) = true := hXin _ (Graph.conj_Normal H.normal)
        have hIP' : Γ.conj.edgeIdx x .plus false = i₁ :: is₂ := by rw [edgeIdx_conj]; exact hIP
        have hL' : Γ.conj.comps[i₁]? = some e₁.conj := by simp [Graph.conj_comps, hL]
        refine hbind ((iOut x Γ.conj i₁ is₂ e₁.conj).map (fun t => ⟨t.nOut, t.g.conj, t.f⟩)) ?_ ?_
          ?_
        · simp [multiEHat, h1, h2, h3, h4, multiEIn_eq hIP' hL' hX', TExpansion.conj]
        · intro T hT
          obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
          exact (H.conj.inTerms Ctx T₀ hT₀).conj
        · rw [List.length_map]
          have := len_iOut x Γ.conj i₁ is₂ e₁.conj
          rw [Graph.conj_comps, List.length_map] at this
          exact this
      · obtain ⟨i₁, is₂, hIP⟩ := List.exists_cons_of_ne_nil h3
        obtain ⟨e₁, hL⟩ := edge_of_idx (x := x) (i := i₁) (ch := .plus) (out := false)
          (by rw [hIP]; exact List.mem_cons_self ..)
        have Ctx : InCtxS C x Γ i₁ is₂ e₁ := ⟨H.normal, H.plain, H.right, H.lf, hIP, hL, h1, h2⟩
        refine hbind (iOut x Γ i₁ is₂ e₁) ?_ (H.inTerms Ctx) (len_iOut x Γ i₁ is₂ e₁)
        simp [multiEHat, h1, h2, h3, multiEIn_eq hIP hL (hXin Γ H.normal)]
    · obtain ⟨i₁, is₂, hOP⟩ := List.exists_cons_of_ne_nil h2
      obtain ⟨e₁, hL⟩ := edge_of_idx (x := x) (i := i₁) (ch := .minus) (out := true)
        (by rw [hOP]; exact List.mem_cons_self ..)
      have Ctx := OutCtxS.conj_of H.normal H.plain H.right H.lf hOP hL
      have hX' : Γ.conj.xdotsAt x (oXIdx x Γ.conj) = true := hXout _ (Graph.conj_Normal H.normal)
      have hOP' : Γ.conj.edgeIdx x .plus true = i₁ :: is₂ := by rw [edgeIdx_conj]; exact hOP
      have hL' : Γ.conj.comps[i₁]? = some e₁.conj := by simp [Graph.conj_comps, hL]
      refine hbind ((oOut x Γ.conj i₁ is₂ e₁.conj).map (fun t => ⟨t.nOut, t.g.conj, t.f⟩)) ?_ ?_
        ?_
      rotate_left 2
      · rw [List.length_map]
        have := len_oOut x Γ.conj i₁ is₂ e₁.conj
        rw [Graph.conj_comps, List.length_map] at this
        exact this
      · simp [multiEHat, h1, h2, multiEOut_eq hOP' hL' hX', TExpansion.conj]
      · intro T hT
        obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
        exact (H.conj.outTerms Ctx T₀ hT₀).conj
  · obtain ⟨i₁, is₂, hOP⟩ := List.exists_cons_of_ne_nil h1
    obtain ⟨e₁, hL⟩ := edge_of_idx (x := x) (i := i₁) (ch := .plus) (out := true)
      (by rw [hOP]; exact List.mem_cons_self ..)
    have Ctx : OutCtxS C x Γ i₁ is₂ e₁ := ⟨H.normal, H.plain, H.right, H.lf, hOP, hL⟩
    refine hbind (oOut x Γ i₁ is₂ e₁) ?_ (H.outTerms Ctx) (len_oOut x Γ i₁ is₂ e₁)
    simp [multiEHat, h1, multiEOut_eq hOP hL (hXout Γ H.normal)]

/-- The step of the multi-edge expansion at `x`. -/
theorem oMultiET_step (H : MEHyp C x Γ) (hX : Γ.XdotApart) (hdeg : 1 ≤ Γ.deg x) :
    ∀ t ∈ oMultiET x Γ, StepOut Γ t := by
  obtain ⟨E, hE, hT, -⟩ := oMultiET_rep H hdeg
  rw [hE]
  exact bind_step hT H.normal H.plain H.lf H.K0 hX

theorem ggbar_input {C : ℕ} {Γ : Graph k n} {x y y' : Atom k n} (hN : Γ.Normal C)
    (h : Γ.GGbarInputAt x y y') :
    (∃ i₁ j : ℕ, ∃ e₁ ej : Comp (Atom k n), Γ.edgeIdx x .plus true = [i₁] ∧
        Γ.edgeIdx x .minus true = [j] ∧ Γ.edgeIdx x .plus false = [] ∧
        Γ.edgeIdx x .minus false = [] ∧ Γ.comps[i₁]? = some e₁ ∧ Γ.comps[j]? = some ej) ∨
    (∃ i₁ j : ℕ, ∃ e₁ ej : Comp (Atom k n), Γ.edgeIdx x .plus true = [] ∧
        Γ.edgeIdx x .minus true = [] ∧ Γ.edgeIdx x .plus false = [i₁] ∧
        Γ.edgeIdx x .minus false = [j] ∧ Γ.comps[i₁]? = some e₁ ∧ Γ.comps[j]? = some ej) := by
  obtain ⟨hdeg, out, ⟨cp, hcp, hkp, hep⟩, ⟨cm, hcm, hkm, hem⟩⟩ := h
  have hsum := deg_eq_sum hN x
  obtain ⟨ip, hip⟩ := idx_of_mem hcp
  obtain ⟨im, him⟩ := idx_of_mem hcm
  have hsp := hN.2.1 cp hcp (by simp [hkp, Kind.isSolid])
  have hsm := hN.2.1 cm hcm (by simp [hkm, Kind.isSolid])
  cases out
  · simp only [Bool.false_eq_true, ite_false] at hep hem
    have hmp : ip ∈ Γ.edgeIdx x .plus false :=
      mem_edgeIdx.2 ⟨cp, hip, hkp, hep.2, fun h => hsp (h.trans hep.2.symm)⟩
    have hmm : im ∈ Γ.edgeIdx x .minus false :=
      mem_edgeIdx.2 ⟨cm, him, hkm, hem.2, fun h => hsm (h.trans hem.2.symm)⟩
    have p1 := List.length_pos_of_mem hmp
    have p2 := List.length_pos_of_mem hmm
    have l1 : (Γ.edgeIdx x .plus false).length = 1 := by omega
    have l2 : (Γ.edgeIdx x .minus false).length = 1 := by omega
    have l3 : (Γ.edgeIdx x .plus true).length = 0 := by omega
    have l4 : (Γ.edgeIdx x .minus true).length = 0 := by omega
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 l1
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 l2
    have hia : ip = a := by rw [ha] at hmp; simpa using hmp
    have hib : im = b := by rw [hb] at hmm; simpa using hmm
    right
    exact ⟨a, b, cp, cm, List.length_eq_zero_iff.1 l3, List.length_eq_zero_iff.1 l4, ha, hb,
      by rw [← hia]; exact hip, by rw [← hib]; exact him⟩
  · simp only [ite_true] at hep hem
    have hmp : ip ∈ Γ.edgeIdx x .plus true :=
      mem_edgeIdx.2 ⟨cp, hip, hkp, hep.1, fun h => hsp (hep.1.trans h.symm)⟩
    have hmm : im ∈ Γ.edgeIdx x .minus true :=
      mem_edgeIdx.2 ⟨cm, him, hkm, hem.1, fun h => hsm (hem.1.trans h.symm)⟩
    have p1 := List.length_pos_of_mem hmp
    have p2 := List.length_pos_of_mem hmm
    have l1 : (Γ.edgeIdx x .plus true).length = 1 := by omega
    have l2 : (Γ.edgeIdx x .minus true).length = 1 := by omega
    have l3 : (Γ.edgeIdx x .plus false).length = 0 := by omega
    have l4 : (Γ.edgeIdx x .minus false).length = 0 := by omega
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 l1
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 l2
    have hia : ip = a := by rw [ha] at hmp; simpa using hmp
    have hib : im = b := by rw [hb] at hmm; simpa using hmm
    left
    exact ⟨a, b, cp, cm, ha, hb, List.length_eq_zero_iff.1 l3, List.length_eq_zero_iff.1 l4,
      by rw [← hia]; exact hip, by rw [← hib]; exact him⟩

/-- The step of the `GḠ` expansion at `x` with the solid edges `G_{xy} Ḡ_{xy'}` or
`G_{yx} Ḡ_{y'x}`. -/
theorem oGGbarT_step (H : MEHyp C x Γ) (hX : Γ.XdotApart) {y y' : Atom k n}
    (hin : Γ.GGbarInputAt x y y') : ∀ t ∈ oGGbarT x Γ, StepOut Γ t := by
  have hdeg := hin.1
  rcases ggbar_input H.normal hin with ⟨i₁, j, e₁, ej, hpt, hmt, hpf, hmf, -, -⟩ |
      ⟨i₁, j, e₁, ej, hpt, hmt, hpf, hmf, -, -⟩
  · have hE : oGGbarT x Γ = oMultiET x Γ := by simp [oGGbarT, hdeg, hpt, hmt, hpf, hmf]
    rw [hE]
    exact oMultiET_step H hX (by omega)
  · have hE : oGGbarT x Γ = oMultiET x Γ := by simp [oGGbarT, hdeg, hpt, hmt, hpf, hmf]
    rw [hE]
    exact oMultiET_step H hX (by omega)

end METerms


/-! ## Bounds on the potential of a term -/

section PhiBounds

variable {k n : ℕ} {Γ : Graph k n} {j : ℕ} {R : List (Comp (Atom k n))}
  {N : List (Comp (Atom k (n + j)))} {lab : Option (Atom k (n + j))} {g : Graph k (n + j)}

private theorem sum_atB_le {m m' : ℕ} {f : Fin m → Atom k m'} (hf : Function.Injective f)
    (L : List (Comp (Atom k m'))) (P : Comp (Atom k m') → Bool) :
    ∑ i : Fin m, (L.filter fun c => P c && atB (f i) c).length ≤ 2 * (L.filter P).length := by
  induction L with
  | nil => simp
  | cons c L ih =>
    have hc : ∑ i : Fin m, (if (P c && atB (f i) c) = true then 1 else 0) ≤
        if P c = true then 2 else 0 := by
      by_cases hP : P c = true
      · rw [if_pos hP]
        have hsub : (Finset.univ.filter fun i => (P c && atB (f i) c) = true) ⊆
            (Finset.univ.filter fun i => f i = c.x) ∪ (Finset.univ.filter fun i => f i = c.y) := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, atB,
            Bool.or_eq_true, beq_iff_eq] at hi
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hi.2 with h | h
          · exact Or.inl h.symm
          · exact Or.inr h.symm
        have h1 : (Finset.univ.filter fun i => f i = c.x).card ≤ 1 :=
          Finset.card_le_one.2 fun a ha b hb => hf (by
            simp only [Finset.mem_filter] at ha hb; rw [ha.2, hb.2])
        have h2 : (Finset.univ.filter fun i => f i = c.y).card ≤ 1 :=
          Finset.card_le_one.2 fun a ha b hb => hf (by
            simp only [Finset.mem_filter] at ha hb; rw [ha.2, hb.2])
        rw [← Finset.card_filter]
        exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))
      · simp [hP]
    have e : ∀ i : Fin m, ((c :: L).filter fun c => P c && atB (f i) c).length =
        (if (P c && atB (f i) c) = true then 1 else 0) +
          (L.filter fun c => P c && atB (f i) c).length := by
      intro i
      rw [List.filter_cons]
      split_ifs <;> simp [add_comm]
    simp only [e, Finset.sum_add_distrib]
    rw [List.filter_cons]
    split_ifs with h
    · simp only [List.length_cons]
      rw [if_pos h] at hc
      omega
    · rw [if_neg h] at hc
      omega

/-- The degrees of a term grow at most by the new solid edges. -/
private theorem Sch.degX_le (hS : Sch Γ j R N lab g)
    (two : ∀ i : Fin j, (N.filter fun c => c.kind.isSolid && atB (newA i) c).length ≤ 2) :
    g.degX ≤ Γ.degX + 2 * (N.filter fun c => c.kind.isSolid).length := by
  rw [degX_lift]
  have hnew : ∑ i : Fin j, (g.deg (newA i) - 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hS.deg_new i]
    have := two i
    omega
  have hold : ∀ i : Fin n, g.deg (liftA j (.inr i)) - 2 ≤ (Γ.deg (.inr i) - 2) +
      (N.filter fun c => c.kind.isSolid && atB (liftA j (.inr i)) c).length := by
    intro i
    have := hS.deg (.inr i)
    omega
  have hsum := sum_atB_le (f := fun i : Fin n => (liftA j (.inr i) : Atom k (n + j)))
    (fun a b h => by simpa using h) N (fun c => c.kind.isSolid)
  rw [hnew, add_zero]
  calc ∑ i : Fin n, (g.deg (liftA j (.inr i)) - 2)
      ≤ ∑ i : Fin n, ((Γ.deg (.inr i) - 2) +
          (N.filter fun c => c.kind.isSolid && atB (liftA j (.inr i)) c).length) :=
        Finset.sum_le_sum fun i _ => hold i
    _ = Γ.degX + ∑ i : Fin n,
          (N.filter fun c => c.kind.isSolid && atB (liftA j (.inr i)) c).length := by
        rw [Finset.sum_add_distrib]; rfl
    _ ≤ Γ.degX + 2 * (N.filter fun c => c.kind.isSolid).length := by omega

/-- The internal atoms of degree `2` that are not standard neutral grow at most by the new atoms
and the atoms touched by the term. -/
private theorem Sch.badN_le (hS : Sch Γ j R N none g) (U : Finset (Fin n))
    (hR : ∀ c ∈ R, ∀ i : Fin n, atB (.inr i) c = true → i ∈ U)
    (hN : ∀ c ∈ N, ∀ i : Fin n, atB (liftA j (.inr i)) c = true → i ∈ U) :
    g.badN ≤ Γ.badN + j + U.card := by
  rw [badN_lift, badN_eq]
  have hnew : ∑ i : Fin j, badI g (newA i) ≤ j := by
    calc ∑ i : Fin j, badI g (newA i) ≤ ∑ _i : Fin j, 1 :=
          Finset.sum_le_sum fun i _ => by unfold badI; split_ifs <;> omega
      _ = j := by simp
  have hold : ∀ i : Fin n, badI g (liftA j (.inr i)) ≤ badI Γ (.inr i) + if i ∈ U then 1 else 0 := by
    intro i
    by_cases hi : i ∈ U
    · rw [if_pos hi]
      have : badI g (liftA j (.inr i)) ≤ 1 := by unfold badI; split_ifs <;> omega
      omega
    · rw [if_neg hi]
      have hu := hS.local_untouched (u := .inr i)
        (fun c hc => by
          by_contra h
          exact hi (hR c hc i (by simpa using h)))
        (fun c hc => by
          by_contra h
          exact hi (hN c hc i (by simpa using h)))
      simp only [badI, hu.1, hu.2]
      exact le_refl _
  have h2 : ∑ i : Fin n, badI g (liftA j (.inr i)) ≤ ∑ i : Fin n, badI Γ (.inr i) + U.card := by
    calc ∑ i : Fin n, badI g (liftA j (.inr i))
        ≤ ∑ i : Fin n, (badI Γ (.inr i) + if i ∈ U then 1 else 0) :=
          Finset.sum_le_sum fun i _ => hold i
      _ = ∑ i : Fin n, badI Γ (.inr i) + U.card := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter]
          simp
  omega

/-- The potential of a term without label. -/
private theorem Sch.phi_le (hS : Sch Γ j R N none g) (U : Finset (Fin n))
    (hR : ∀ c ∈ R, ∀ i : Fin n, atB (.inr i) c = true → i ∈ U)
    (hN : ∀ c ∈ N, ∀ i : Fin n, atB (liftA j (.inr i)) c = true → i ∈ U)
    (two : ∀ i : Fin j, (N.filter fun c => c.kind.isSolid && atB (newA i) c).length ≤ 2) :
    g.phi + 1000 * (R.filter fun c => c.kind.isLt).length + (R.filter fun c => c.kind.isRg).length ≤
      Γ.phi + 1000 * (N.filter fun c => c.kind.isLt).length +
        (N.filter fun c => c.kind.isRg).length +
        200 * (N.filter fun c => c.kind.isSolid).length + 10 * (j + U.card) := by
  have h1 := hS.lwN
  have h2 := hS.rwN
  have h3 := hS.degX_le two
  have h4 := hS.badN_le U hR hN
  unfold Graph.phi
  omega

/-- The atoms of a list, as a set of internal atoms. -/
private def intSet (l : List (Atom k n)) : Finset (Fin n) := (l.filterMap Sum.getRight?).toFinset

private theorem mem_intSet {l : List (Atom k n)} {i : Fin n} : i ∈ intSet l ↔ (.inr i : Atom k n) ∈ l := by
  unfold intSet
  rw [List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, h⟩
    rcases a with a | a
    · simp at h
    · simp only [Sum.getRight?_inr, Option.some.injEq] at h
      subst h; exact ha
  · intro h
    exact ⟨_, h, rfl⟩

private theorem card_intSet_le (l : List (Atom k n)) : (intSet l).card ≤ l.length := by
  unfold intSet
  exact (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

end PhiBounds

/-! ## The terms of the light weight expansion -/

section W2Defs

variable {k n : ℕ}

/-- The terms of [I, (3.5)] for the light weight of charge `plus` on `x` at the index `i`. -/
def w2Out (x : Atom k n) (Γ : Graph k n) (i : ℕ) : TExpansion k n :=
  [t1 (liftCs 1 Γ.comps ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.light .plus) (newA 0) (newA 0)]) (cm * Γ.coeff),
    t2 (liftCs 2 (Γ.comps.eraseIdx i) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
      mkC (.light .plus) (newA 1) (newA 1)]) (cm * Γ.coeff)] ++
  (dTerms (newA 0) (liftA 1 x) (liftCs 1 (Γ.comps.eraseIdx i))).map (fun d =>
    t1 (d ++ [mkC (.waved .s) (liftA 1 x) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 x)])
      (cm * Γ.coeff)) ++
  (dTerms (newA 1) (newA 0) (liftCs 2 (Γ.comps.eraseIdx i))).map (fun d =>
    t2 (d ++ [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1),
      mkC (.G .plus) (newA 1) (newA 0)]) (cm * Γ.coeff)) ++
  [⟨n, ⟨labelQs x Γ.comps, Γ.coeff⟩, id⟩,
    t1 (labelQs (newA 0) (liftCs 1 (Γ.comps.eraseIdx i) ++ [mkC (.light .plus) (newA 0) (newA 0)]) ++
      [mkC (.waved .plus) (liftA 1 x) (newA 0)]) Γ.coeff,
    t1 (labelQs (liftA 1 x) (liftCs 1 (Γ.comps.eraseIdx i) ++ [mkC (.light .plus) (newA 0) (newA 0),
      mkC (.weight .plus) (liftA 1 x) (liftA 1 x)]) ++ [mkC (.waved .s) (liftA 1 x) (newA 0)])
      (-cm * Γ.coeff),
    t2 (labelQs (newA 0) (liftCs 2 (Γ.comps.eraseIdx i) ++ [mkC (.light .plus) (newA 1) (newA 1),
      mkC (.weight .plus) (newA 0) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)]) (-cm * Γ.coeff)] ++
  (dTerms (newA 0) (liftA 1 x) (liftCs 1 (Γ.comps.eraseIdx i))).map (fun d =>
    t1 (labelQs (liftA 1 x) (d ++ [mkC (.G .plus) (newA 0) (liftA 1 x)]) ++
      [mkC (.waved .s) (liftA 1 x) (newA 0)]) (-cm * Γ.coeff)) ++
  (dTerms (newA 1) (newA 0) (liftCs 2 (Γ.comps.eraseIdx i))).map (fun d =>
    t2 (labelQs (newA 0) (d ++ [mkC (.G .plus) (newA 1) (newA 0)]) ++
      [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)]) (-cm * Γ.coeff))

theorem oWeight2Pos_eq {x : Atom k n} {Γ : Graph k n} {i : ℕ}
    (h : Γ.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) = some i) :
    oWeight2Pos x Γ = some (w2Out x Γ i) := by
  unfold oWeight2Pos
  rw [h]
  rfl

theorem oWeight2Pos_none {x : Atom k n} {Γ : Graph k n}
    (h : Γ.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) = none) :
    oWeight2Pos x Γ = none := by
  unfold oWeight2Pos
  rw [h]

end W2Defs

section LengthsW

variable {k n : ℕ}

end LengthsW

section W2Terms

variable {k n : ℕ}

/-- The data of the light weight expansion at `x`: `Γ` is plain, normal regular with bound `C`,
without labels, every random component has an internal first atom, `x` is internal and the
component at the index `i` is a light weight of charge `plus` on `x`. -/
structure WCtx (C : ℕ) (x : Atom k n) (Γ : Graph k n) (i : ℕ) (ℓ : Comp (Atom k n)) : Prop where
  normal : Γ.Normal C
  plain : Γ.Plain
  lf : Γ.LabelFree
  K0 : Γ.RandomFirstInt
  right : x.isRight = true
  hi : Γ.comps[i]? = some ℓ
  hk : ℓ.kind = .light .plus
  hx : ℓ.x = x

variable {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i : ℕ} {ℓ : Comp (Atom k n)}

theorem WCtx.mem (H : WCtx C x Γ i ℓ) : ℓ ∈ Γ.comps := List.mem_of_getElem? H.hi

private theorem WCtx.hy (H : WCtx C x Γ i ℓ) : ℓ.y = x := by
  have := (H.plain ℓ H.mem).2.2.2.2.1 (by rw [H.hk]; rfl)
  rw [this, H.hx]

theorem WCtx.perm1 (H : WCtx C x Γ i ℓ) : Γ.comps.Perm (Γ.comps.eraseIdx i ++ [ℓ]) :=
  (eraseIdx_perm H.hi).symm

/-- `m ∑_α s_{xα} (G_{αα} - m) 𝒢`, at any atom `x`. -/
private theorem termSL (hx : x.isRight = true) (co : Coeff) :
    TermOK Γ x (t1 (liftCs 1 Γ.comps ++ [mkC (.waved .s) (liftA 1 x) (newA 0),
      mkC (.light .plus) (newA 0) (newA 0)]) co) := by
  refine termOK_mk (K := Γ.comps) (R := []) none [mkC (.waved .s) (liftA 1 x) (newA 0),
    mkC (.light .plus) (newA 0) (newA 0)] [] _ 1 (by simp) (by simp) (by simp [labW]) (by simp)
    ?_ ?_ ?_ ?_ (fun _ _ => false) (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨NewOK_waved _ _ _, rfl⟩
    · exact ⟨NewOK_light _ _, rfl⟩
  · intro c hc hr
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp_all [mkC, Kind.isRandom]
  · simp [ordL, mkC, Kind.ord]
  · intro i; simp [mkC, Kind.isSolid]
  · simp [mkC, Kind.isSolid]
  · simp [mkC, Kind.isSolid]
  · intro h; simp at h
  · simp [mkC, Kind.isSolid]
  · intro _ h; simp at h
  · intro h; simp at h
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact sameMol_of_waved (w := .s) (List.mem_append_right _ (List.mem_cons_self ..))
      (by simpa using hx) rfl

/-- The terms of [I, (3.5)] with the light weight `ℓ` replaced by new components without solid
edge: `N₁` (labelled by `lab`) and the waved edges `N₂`. -/
private theorem WCtx.termNS (H : WCtx C x Γ i ℓ) {j : ℕ} (lab : Option (Atom k (n + j)))
    (N₁ N₂ : List (Comp (Atom k (n + j)))) (co : Coeff) (s : ℕ)
    {cs : List (Comp (Atom k (n + j)))}
    (hcs : cs.Perm (labW lab (liftCs j (Γ.comps.eraseIdx i) ++ N₁) ++ N₂))
    (hN₂ : ∀ c ∈ N₂, c.kind.isRandom = false)
    (hNo : ∀ c ∈ N₁ ++ N₂, NewOK c ∧ c.label = none)
    (hNK : ∀ c ∈ N₁ ++ N₂, c.kind.isRandom = true → c.x.isRight = true)
    (hs : ordL (N₁ ++ N₂) = 1 + 2 * j + s)
    (hsol : ((N₁ ++ N₂).filter fun c => c.kind.isSolid) = [])
    (hphi : lab = none → s = 0 → (⟨cs, co⟩ : Graph k (n + j)).phi + 3 ≤ Γ.phi)
    (hlab : lab ≠ none → ∃ c ∈ N₁, c.kind.isRandom = true)
    (att : ∀ i : Fin j, (⟨cs, co⟩ : Graph k (n + j)).SameMol (liftA j x) (newA i)) :
    TermOK Γ x ⟨n + j, ⟨cs, co⟩, liftA j⟩ := by
  have hz : ∀ P : Comp (Atom k (n + j)) → Bool,
      ((N₁ ++ N₂).filter fun c => c.kind.isSolid && P c) = [] := by
    intro P
    rw [List.filter_eq_nil_iff]
    intro c hc h
    have : c ∈ (N₁ ++ N₂).filter fun c => c.kind.isSolid := List.mem_filter.2 ⟨hc, by
      simp only [Bool.and_eq_true] at h; exact h.1⟩
    rw [hsol] at this
    simp at this
  refine termOK_mk (K := Γ.comps.eraseIdx i) (R := [ℓ]) lab N₁ N₂ co s H.perm1
    (by simp [H.hk, Kind.isRandom]) hcs hN₂ hNo hNK (by rw [hs]; simp [ordL, H.hk, Kind.ord])
    (fun i' => by rw [hz]; simp) (fun _ _ => false) (by simp) ?_ (by rw [hsol]; simp)
    (fun _ => by rw [hsol]; simp) ?_ hphi ?_ att
  · have := hz (fun c => !isNewA n c.x && !isNewA n c.y && !false)
    simp only [Bool.and_assoc] at this ⊢
    rw [this]; simp
  · rw [hz]; simp
  · intro hl
    obtain ⟨c, hc, hr⟩ := hlab hl
    obtain ⟨u, rfl⟩ := Option.ne_none_iff_exists'.1 hl
    refine ⟨c.labelQ u, hcs.mem_iff.2 (List.mem_append_left _ ?_), by simp [Comp.labelQ, hr]⟩
    simp only [labW, labelQs]
    exact List.mem_map_of_mem (List.mem_append_right _ hc)

/-- `m ∑_{α,β} S⁺_{xα} s_{αβ} (G_{αα} - m)(G_{ββ} - m) f`. -/
private theorem WCtx.termW2 (H : WCtx C x Γ i ℓ) (co : Coeff) :
    TermOK Γ x (t2 (liftCs 2 (Γ.comps.eraseIdx i) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
      mkC (.light .plus) (newA 1) (newA 1)]) co) := by
  have hx := H.right
  refine H.termNS none [mkC (.light .plus) (newA 0) (newA 0), mkC (.light .plus) (newA 1) (newA 1)]
    [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)] co 1 ?_
    (by simp [mkC, Kind.isRandom]) ?_ ?_ (by simp [ordL, mkC, Kind.ord])
    (by simp [mkC, Kind.isSolid]) (fun _ h => by simp at h) (fun h => absurd rfl h) ?_
  · simp only [labW, List.append_assoc]
    exact List.Perm.append_left _ (List.perm_append_comm (l₁ := [_, _]) (l₂ := [_, _]))
  · intro c hc
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨NewOK_light _ _, rfl⟩
    · exact ⟨NewOK_light _ _, rfl⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
  · intro c hc hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> simp_all [mkC, Kind.isRandom]
  · have hmem1 : mkC (.waved .plus) (liftA 2 x) (newA 0) ∈
        (⟨liftCs 2 (Γ.comps.eraseIdx i) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
          mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
          mkC (.light .plus) (newA 1) (newA 1)], co⟩ : Graph k (n + 2)).comps := by simp
    have hmem2 : mkC (.waved .s) (newA 0) (newA 1) ∈
        (⟨liftCs 2 (Γ.comps.eraseIdx i) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
          mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
          mkC (.light .plus) (newA 1) (newA 1)], co⟩ : Graph k (n + 2)).comps := by simp
    have a0 := sameMol_of_waved hmem1 (by simpa using hx) (isRight_newA _)
    have a1 := sameMol_of_waved hmem2 (isRight_newA _) (isRight_newA _)
    intro i
    fin_cases i
    · exact a0
    · exact (Graph.sameMol_equivalence _).trans a0 a1

/-- The `Q`-term `Q_α ((G_{αα} - m) f) S⁺_{xα}`. -/
private theorem WCtx.termQ2 (H : WCtx C x Γ i ℓ) (co : Coeff) :
    TermOK Γ x (t1 (labelQs (newA 0) (liftCs 1 (Γ.comps.eraseIdx i) ++
      [mkC (.light .plus) (newA 0) (newA 0)]) ++ [mkC (.waved .plus) (liftA 1 x) (newA 0)]) co) := by
  have hx := H.right
  refine H.termNS (some (newA 0)) [mkC (.light .plus) (newA 0) (newA 0)]
    [mkC (.waved .plus) (liftA 1 x) (newA 0)] co 0 (List.Perm.refl _)
    (by simp [mkC, Kind.isRandom]) ?_ ?_ (by simp [ordL, mkC, Kind.ord])
    (by simp [mkC, Kind.isSolid]) (fun h => by simp at h)
    (fun _ => ⟨_, List.mem_cons_self .., rfl⟩) ?_
  · intro c hc
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨NewOK_light _ _, rfl⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
  · intro c hc hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp_all [mkC, Kind.isRandom]
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact sameMol_of_waved (List.mem_append_right _ (List.mem_singleton_self _))
      (by simpa using hx) rfl

/-- The `Q`-term `-m Q_x ((G_{αα} - m) G_{xx} f) s_{xα}`. -/
private theorem WCtx.termQ3 (H : WCtx C x Γ i ℓ) (co : Coeff) :
    TermOK Γ x (t1 (labelQs (liftA 1 x) (liftCs 1 (Γ.comps.eraseIdx i) ++
      [mkC (.light .plus) (newA 0) (newA 0), mkC (.weight .plus) (liftA 1 x) (liftA 1 x)]) ++
      [mkC (.waved .s) (liftA 1 x) (newA 0)]) co) := by
  have hx := H.right
  refine H.termNS (some (liftA 1 x)) [mkC (.light .plus) (newA 0) (newA 0),
    mkC (.weight .plus) (liftA 1 x) (liftA 1 x)] [mkC (.waved .s) (liftA 1 x) (newA 0)] co 0
    (List.Perm.refl _) (by simp [mkC, Kind.isRandom]) ?_ ?_
    (by simp [ordL, mkC, Kind.ord]) (by simp [mkC, Kind.isSolid]) (fun h => by simp at h)
    (fun _ => ⟨_, List.mem_cons_self .., rfl⟩) ?_
  · intro c hc
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨NewOK_light _ _, rfl⟩
    · exact ⟨NewOK_weight _ _, rfl⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
  · intro c hc hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> simp_all [mkC, Kind.isRandom]
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact sameMol_of_waved (List.mem_append_right _ (List.mem_singleton_self _))
      (by simpa using hx) rfl

/-- The `Q`-term `-m Q_α ((G_{ββ} - m) G_{αα} f) S⁺_{xα} s_{αβ}`. -/
private theorem WCtx.termQ4 (H : WCtx C x Γ i ℓ) (co : Coeff) :
    TermOK Γ x (t2 (labelQs (newA 0) (liftCs 2 (Γ.comps.eraseIdx i) ++
      [mkC (.light .plus) (newA 1) (newA 1), mkC (.weight .plus) (newA 0) (newA 0)]) ++
      [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)]) co) := by
  have hx := H.right
  refine H.termNS (some (newA 0)) [mkC (.light .plus) (newA 1) (newA 1),
    mkC (.weight .plus) (newA 0) (newA 0)]
    [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)] co 0
    (List.Perm.refl _) (by simp [mkC, Kind.isRandom]) ?_ ?_
    (by simp [ordL, mkC, Kind.ord]) (by simp [mkC, Kind.isSolid]) (fun h => by simp at h)
    (fun _ => ⟨_, List.mem_cons_self .., rfl⟩) ?_
  · intro c hc
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨NewOK_light _ _, rfl⟩
    · exact ⟨NewOK_weight _ _, rfl⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
    · exact ⟨NewOK_waved _ _ _, rfl⟩
  · intro c hc hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> simp_all [mkC, Kind.isRandom]
  · have hmem1 : mkC (.waved .plus) (liftA 2 x) (newA 0) ∈ (⟨labelQs (newA 0)
        (liftCs 2 (Γ.comps.eraseIdx i) ++ [mkC (.light .plus) (newA 1) (newA 1),
        mkC (.weight .plus) (newA 0) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1)], co⟩ : Graph k (n + 2)).comps := by simp
    have hmem2 : mkC (.waved .s) (newA 0) (newA 1) ∈ (⟨labelQs (newA 0)
        (liftCs 2 (Γ.comps.eraseIdx i) ++ [mkC (.light .plus) (newA 1) (newA 1),
        mkC (.weight .plus) (newA 0) (newA 0)]) ++ [mkC (.waved .plus) (liftA 2 x) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1)], co⟩ : Graph k (n + 2)).comps := by simp
    have a0 := sameMol_of_waved hmem1 (by simpa using hx) (isRight_newA _)
    have a1 := sameMol_of_waved hmem2 (isRight_newA _) (isRight_newA _)
    intro i
    fin_cases i
    · exact a0
    · exact (Graph.sameMol_equivalence _).trans a0 a1

end W2Terms

section W2DTerms

variable {k n : ℕ} {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i : ℕ} {ℓ : Comp (Atom k n)}

private theorem intSet_of_endsN {j : ℕ} {L : List (Atom k n)} {N : List (Comp (Atom k (n + j)))}
    (h : ∀ c ∈ N, ∀ u, (u = c.x ∨ u = c.y) → isNewA n u = true ∨ ∃ v ∈ L, u = liftA j v) :
    ∀ c ∈ N, ∀ i : Fin n, atB (liftA j (.inr i)) c = true → i ∈ intSet L := by
  intro c hc i hat
  have hu : liftA j (.inr i) = c.x ∨ liftA j (.inr i) = c.y := by
    simp only [atB, Bool.or_eq_true, beq_iff_eq] at hat
    rcases hat with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  rcases h c hc _ hu with h' | ⟨v, hv, hv'⟩
  · simp at h'
  · rw [mem_intSet]
    rw [liftA_inj'] at hv'
    rw [hv']; exact hv

private theorem intSet_of_endsR {L : List (Atom k n)} {R : List (Comp (Atom k n))}
    (h : ∀ c ∈ R, c.x ∈ L ∧ c.y ∈ L) :
    ∀ c ∈ R, ∀ i : Fin n, atB (.inr i) c = true → i ∈ intSet L := by
  intro c hc i hat
  rw [mem_intSet]
  simp only [atB, Bool.or_eq_true, beq_iff_eq] at hat
  rcases hat with h' | h'
  · rw [← h']; exact (h c hc).1
  · rw [← h']; exact (h c hc).2

/-- The derivative terms `-m ∑_α s_{xα} G_{αx} ∂_{h_{αx}} f` of [I, (3.5)], without or with the
label `Q_x`. -/
private theorem WCtx.termD1 (H : WCtx C x Γ i ℓ) {d : List (Comp (Atom k (n + 1)))}
    (hd : d ∈ dTerms (newA 0) (liftA 1 x) (liftCs 1 (Γ.comps.eraseIdx i)))
    (lab : Option (Atom k (n + 1))) (hlab : lab = none ∨ lab = some (liftA 1 x))
    {cs : List (Comp (Atom k (n + 1)))}
    (hcs : cs.Perm (labW lab (d ++ [mkC (.G .plus) (newA 0) (liftA 1 x)]) ++
      [mkC (.waved .s) (liftA 1 x) (newA 0)])) (co : Coeff) :
    TermOK Γ x (t1 cs co) := by
  have hxR := H.right
  have hxL : x.isLeft = false := by cases x <;> simp_all
  obtain ⟨c₀, K, ps, hF, hc₀, hps, rfl⟩ := dTerms_lift_split hd
  have hc₀m : c₀ ∈ Γ.comps := List.mem_of_mem_eraseIdx hc₀
  have hpm := dPieces_lift hps
  have hr₀ : c₀.kind.isRandom = true := by
    rcases hpm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact (kind_ord_of_pm h).2.2
  have hcxR : c₀.x.isRight = true := H.K0 c₀ hc₀m hr₀
  have hcxL : c₀.x.isLeft = false := by cases h : c₀.x <;> simp_all
  have hperm : Γ.comps.Perm (K ++ [ℓ, c₀]) := by
    refine H.perm1.trans ?_
    refine (hF.append_right _).trans ?_
    rw [List.append_assoc]
    exact List.Perm.append_left K (List.perm_append_comm (l₁ := [c₀]) (l₂ := [ℓ]))
  have hord : c₀.kind.ord = 1 ∨ c₀.kind.ord = 0 := by
    rcases hpm with ⟨h, -⟩ | ⟨h, -⟩
    · rcases h with h | h | h <;> exact (kind_ord_of_pm (ch := .plus) (by simp [h])).1
    · rcases h with h | h | h <;> exact (kind_ord_of_pm (ch := .minus) (by simp [h])).1
  have hwB : c₀.kind.isSolid = false → c₀.endB = c₀.x := by
    intro hs
    have : c₀.kind.isWeight = true := by
      rcases hpm with ⟨h, -⟩ | ⟨h, -⟩ <;> rcases h with h | h | h <;>
        simp_all [Kind.isSolid, Kind.isWeight]
    simp [Comp.endB, this]
  have hbS : c₀.kind.isSolid = true → c₀.endB = c₀.y := by
    intro hs
    have : c₀.kind.isWeight = false := by
      revert hs; cases c₀.kind <;> simp [Kind.isSolid, Kind.isWeight]
    simp [Comp.endB, this]
  have hBL : c₀.endB.isLeft = true → c₀.kind.isSolid = true ∧ c₀.y.isLeft = true := by
    intro h
    by_cases hs : c₀.kind.isSolid = true
    · exact ⟨hs, by rw [← hbS hs]; exact h⟩
    · rw [hwB (by simpa using hs), hcxL] at h; cases h
  have hsh : (ps = [mkC (.G .plus) (liftA 1 c₀.x) (newA 0),
        mkC (.G .plus) (liftA 1 x) (liftA 1 c₀.endB)] ∧ c₀.endB ≠ x) ∨
      (ps = [mkC (.G .plus) (liftA 1 c₀.x) (newA 0),
        mkC (.weight .plus) (liftA 1 x) (liftA 1 x)] ∧ c₀.endB = x) ∨
      (ps = [mkC (.G .minus) (liftA 1 c₀.x) (liftA 1 x),
        mkC (.G .minus) (newA 0) (liftA 1 c₀.endB)] ∧ c₀.x ≠ x) ∨
      (ps = [mkC (.weight .minus) (liftA 1 x) (liftA 1 x),
        mkC (.G .minus) (newA 0) (liftA 1 c₀.endB)] ∧ c₀.x = x) := by
    rcases hpm with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · rw [solidC_of_ne (by simp)]
      by_cases hb : c₀.endB = x
      · right; left; rw [hb, solidC_self]; exact ⟨rfl, rfl⟩
      · left
        rw [solidC_of_ne (fun h => hb ((liftA_injective 1 h).symm))]
        exact ⟨rfl, hb⟩
    · rw [solidC_of_ne (show (newA 0 : Atom k (n + 1)) ≠ liftA 1 c₀.endB by simp)]
      by_cases hb : c₀.x = x
      · right; right; right; rw [hb, solidC_self]; exact ⟨rfl, rfl⟩
      · right; right; left
        rw [solidC_of_ne (fun h => hb (liftA_injective 1 h))]
        exact ⟨rfl, hb⟩
  have hop : ordL ps = 1 ∨ ordL ps = 2 := by
    rcases hsh with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [mkC, Kind.ord]
  obtain ⟨s, hs⟩ : ∃ s : ℕ, ordL ps = c₀.kind.ord + s :=
    ⟨(ordL ps - c₀.kind.ord).toNat, by omega⟩
  have hR : ∀ c ∈ [ℓ, c₀], c.kind.isRandom = true := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · simp [H.hk, Kind.isRandom]
    · exact hr₀
  have hcs' : cs.Perm (labW lab (liftCs 1 K ++ (ps ++ [mkC (.G .plus) (newA 0) (liftA 1 x)])) ++
      [mkC (.waved .s) (liftA 1 x) (newA 0)]) :=
    hcs.trans (List.Perm.of_eq (by simp [List.append_assoc]))
  have two : ∀ i : Fin 1, (((ps ++ [mkC (.G .plus) (newA 0) (liftA 1 x)]) ++
      [mkC (.waved .s) (liftA 1 x) (newA 0)]).filter
        fun c => c.kind.isSolid && atB (newA i) c).length ≤ 2 := by
    intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rcases hsh with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [mkC, Kind.isSolid, atB]
  refine termOK_mk (K := K) (R := [ℓ, c₀]) lab (ps ++ [mkC (.G .plus) (newA 0) (liftA 1 x)])
    [mkC (.waved .s) (liftA 1 x) (newA 0)] co s hperm hR hcs' (by simp [mkC, Kind.isRandom])
    ?_ ?_ ?_ two (fun _ _ => false) (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- new components
    intro c hc
    rw [List.mem_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · refine ⟨dPieces_newOK hps c hc, ?_⟩
      rcases hsh with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
         rcases hc with rfl | rfl <;> rfl)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      exact ⟨NewOK_G _ (by simp), rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      exact ⟨NewOK_waved _ _ _, rfl⟩
  · -- first atoms
    intro c hc hr
    rw [List.mem_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · rcases hsh with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
         rcases hc with rfl | rfl <;> simp [mkC, hcxR, hxR])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp [mkC]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp [mkC, Kind.isRandom] at hr
  · -- order
    simp only [ordL_append, hs, ordL_cons, ordL_nil, H.hk]
    simp [mkC, Kind.ord]
    ring
  · -- solid edges between old atoms
    have oG : ∀ ch, (Kind.G ch).ord = 1 := fun _ => rfl
    have oW : ∀ ch, (Kind.weight ch).ord = 0 := fun _ => rfl
    rcases hsh with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      simp only [ordL_cons, ordL_nil, mkC, oG, oW] at hs <;>
      simp [mkC, Kind.isSolid] <;> omega
  · rcases hsh with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [mkC, Kind.isSolid]
  · intro hs0
    subst hs0
    have oG : ∀ ch, (Kind.G ch).ord = 1 := fun _ => rfl
    have oW : ∀ ch, (Kind.weight ch).ord = 0 := fun _ => rfl
    rcases hsh with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
      simp only [ordL_cons, ordL_nil, mkC, oG, oW] at hs <;>
      simp [mkC, Kind.isSolid] <;> omega
  · -- solid edges at external atoms
    have hRc : ([ℓ, c₀].filter fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length =
        if c₀.kind.isSolid && c₀.y.isLeft then 1 else 0 := by
      simp only [List.filter_cons, List.filter_nil, H.hk, Kind.isSolid, hcxL, Bool.false_or]
      split_ifs <;> simp_all
    rw [hRc]
    by_cases hE : c₀.endB.isLeft = true
    · obtain ⟨hs', hy⟩ := hBL hE
      rw [if_pos (by simp [hs', hy])]
      rcases hsh with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
        simp [mkC, Kind.isSolid, hxL, hcxL, hE]
    · simp only [Bool.not_eq_true] at hE
      rcases hsh with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
        simp [mkC, Kind.isSolid, hxL, hcxL, hE]
  · -- the potential
    intro hl hs0
    subst hl
    have hS := sch_mk (j := 1) hR hperm none (ps ++ [mkC (.G .plus) (newA 0) (liftA 1 x)])
      [mkC (.waved .s) (liftA 1 x) (newA 0)] (by simp [mkC, Kind.isRandom]) hcs' co
    have hRU := intSet_of_endsR (L := [x, c₀.x, c₀.y, c₀.endB]) (R := [ℓ, c₀]) (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · simp [H.hx, H.hy]
      · simp)
    have hNU := intSet_of_endsN (j := 1) (L := [x, c₀.x, c₀.y, c₀.endB])
      (N := (ps ++ [mkC (.G .plus) (newA 0) (liftA 1 x)]) ++ [mkC (.waved .s) (liftA 1 x) (newA 0)])
      (by
        intro c hc u hu
        rcases hsh with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
          (simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
           rcases hc with ((rfl | rfl) | rfl) | rfl <;>
             (rcases hu with rfl | rfl <;> simp [mkC])))
    have hle := hS.phi_le _ hRU hNU two
    have hU : (intSet [x, c₀.x, c₀.y, c₀.endB]).card ≤ 4 := card_intSet_le _
    have hlt : 1 ≤ ([ℓ, c₀].filter fun c => c.kind.isLt).length := by
      simp [List.filter_cons, H.hk, Kind.isLt]
    have hN1 : (((ps ++ [mkC (.G .plus) (newA 0) (liftA 1 x)]) ++
        [mkC (.waved .s) (liftA 1 x) (newA 0)]).filter fun c => c.kind.isLt).length = 0 ∧
        (((ps ++ [mkC (.G .plus) (newA 0) (liftA 1 x)]) ++
        [mkC (.waved .s) (liftA 1 x) (newA 0)]).filter fun c => c.kind.isRg).length ≤ 1 ∧
        (((ps ++ [mkC (.G .plus) (newA 0) (liftA 1 x)]) ++
        [mkC (.waved .s) (liftA 1 x) (newA 0)]).filter fun c => c.kind.isSolid).length ≤ 3 := by
      rcases hsh with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
        simp [mkC, Kind.isLt, Kind.isRg, Kind.isSolid]
    omega
  · intro hl
    rcases hlab with h | h
    · exact absurd h hl
    · subst h
      refine ⟨(mkC (.G .plus) (newA 0) (liftA 1 x)).labelQ (liftA 1 x), hcs.mem_iff.2 ?_, ?_⟩
      · apply List.mem_append_left
        simp only [labW, labelQs]
        exact List.mem_map_of_mem (by simp)
      · simp [Comp.labelQ, mkC, Kind.isRandom]
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact sameMol_of_waved (g := ⟨cs, co⟩) (hcs.mem_iff.2 (List.mem_append_right _
      (List.mem_singleton_self _))) (by simpa using hxR) rfl

/-- The derivative terms `-m ∑_{α,β} S⁺_{xα} s_{αβ} G_{βα} ∂_{h_{βα}} f` of [I, (3.5)], without or
with the label `Q_α`. -/
private theorem WCtx.termD2 (H : WCtx C x Γ i ℓ) {d : List (Comp (Atom k (n + 2)))}
    (hd : d ∈ dTerms (newA 1) (newA 0) (liftCs 2 (Γ.comps.eraseIdx i)))
    (lab : Option (Atom k (n + 2))) (hlab : lab = none ∨ lab = some (newA 0))
    {cs : List (Comp (Atom k (n + 2)))}
    (hcs : cs.Perm (labW lab (d ++ [mkC (.G .plus) (newA 1) (newA 0)]) ++
      [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)])) (co : Coeff) :
    TermOK Γ x (t2 cs co) := by
  have hxR := H.right
  have hxL : x.isLeft = false := by cases x <;> simp_all
  obtain ⟨c₀, K, ps, hF, hc₀, hps, rfl⟩ := dTerms_lift_split hd
  have hc₀m : c₀ ∈ Γ.comps := List.mem_of_mem_eraseIdx hc₀
  have hpm := dPieces_lift hps
  have hr₀ : c₀.kind.isRandom = true := by
    rcases hpm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact (kind_ord_of_pm h).2.2
  have hcxR : c₀.x.isRight = true := H.K0 c₀ hc₀m hr₀
  have hcxL : c₀.x.isLeft = false := by cases h : c₀.x <;> simp_all
  have hperm : Γ.comps.Perm (K ++ [ℓ, c₀]) := by
    refine H.perm1.trans ?_
    refine (hF.append_right _).trans ?_
    rw [List.append_assoc]
    exact List.Perm.append_left K (List.perm_append_comm (l₁ := [c₀]) (l₂ := [ℓ]))
  have hord : c₀.kind.ord = 1 ∨ c₀.kind.ord = 0 := by
    rcases hpm with ⟨h, -⟩ | ⟨h, -⟩
    · rcases h with h | h | h <;> exact (kind_ord_of_pm (ch := .plus) (by simp [h])).1
    · rcases h with h | h | h <;> exact (kind_ord_of_pm (ch := .minus) (by simp [h])).1
  have hwB : c₀.kind.isSolid = false → c₀.endB = c₀.x := by
    intro hs
    have : c₀.kind.isWeight = true := by
      rcases hpm with ⟨h, -⟩ | ⟨h, -⟩ <;> rcases h with h | h | h <;>
        simp_all [Kind.isSolid, Kind.isWeight]
    simp [Comp.endB, this]
  have hbS : c₀.kind.isSolid = true → c₀.endB = c₀.y := by
    intro hs
    have : c₀.kind.isWeight = false := by
      revert hs; cases c₀.kind <;> simp [Kind.isSolid, Kind.isWeight]
    simp [Comp.endB, this]
  have hBL : c₀.endB.isLeft = true → c₀.kind.isSolid = true ∧ c₀.y.isLeft = true := by
    intro h
    by_cases hs : c₀.kind.isSolid = true
    · exact ⟨hs, by rw [← hbS hs]; exact h⟩
    · rw [hwB (by simpa using hs), hcxL] at h; cases h
  have hsh : ps = [mkC (.G .plus) (liftA 2 c₀.x) (newA 1),
        mkC (.G .plus) (newA 0) (liftA 2 c₀.endB)] ∨
      ps = [mkC (.G .minus) (liftA 2 c₀.x) (newA 0),
        mkC (.G .minus) (newA 1) (liftA 2 c₀.endB)] := by
    rcases hpm with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · left; rw [solidC_of_ne (by simp), solidC_of_ne (by simp)]
    · right; rw [solidC_of_ne (by simp), solidC_of_ne (by simp)]
  have hR : ∀ c ∈ [ℓ, c₀], c.kind.isRandom = true := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · simp [H.hk, Kind.isRandom]
    · exact hr₀
  have hcs' : cs.Perm (labW lab (liftCs 2 K ++ (ps ++ [mkC (.G .plus) (newA 1) (newA 0)])) ++
      [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)]) :=
    hcs.trans (List.Perm.of_eq (by simp [List.append_assoc]))
  refine termOK_mk (K := K) (R := [ℓ, c₀]) lab (ps ++ [mkC (.G .plus) (newA 1) (newA 0)])
    [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)] co
    (2 - c₀.kind.ord).toNat hperm hR hcs' (by simp [mkC, Kind.isRandom])
    ?_ ?_ ?_ ?_ (fun _ _ => false) (by simp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro c hc
    rw [List.mem_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · refine ⟨dPieces_newOK hps c hc, ?_⟩
      rcases hsh with rfl | rfl <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
         rcases hc with rfl | rfl <;> rfl)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      exact ⟨NewOK_G _ (by simp), rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ⟨NewOK_waved _ _ _, rfl⟩
      · exact ⟨NewOK_waved _ _ _, rfl⟩
  · intro c hc hr
    rw [List.mem_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · rcases hsh with rfl | rfl <;>
        (simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
         rcases hc with rfl | rfl <;> simp [mkC, hcxR])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp [mkC]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [mkC, Kind.isRandom] at hr
  · have hN : ordL ((ps ++ [mkC (.G .plus) (newA 1) (newA 0)]) ++
        [mkC (.waved .plus) (liftA 2 x) (newA 0), mkC (.waved .s) (newA 0) (newA 1)]) = 7 := by
      rcases hsh with rfl | rfl <;> simp [mkC, Kind.ord] <;> norm_num
    rw [hN]
    simp only [ordL_cons, ordL_nil, H.hk]
    rcases hord with h | h <;> rw [h] <;> simp [Kind.ord] <;> norm_num
  · intro i
    rcases hsh with rfl | rfl <;> fin_cases i <;> simp [mkC, Kind.isSolid, atB]
  · rcases hsh with rfl | rfl <;> simp [mkC, Kind.isSolid]
  · rcases hsh with rfl | rfl <;> simp [mkC, Kind.isSolid]
  · intro h
    rcases hord with h' | h' <;> rw [h'] at h <;> simp at h
  · have hRc : ([ℓ, c₀].filter fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)).length =
        if c₀.kind.isSolid && c₀.y.isLeft then 1 else 0 := by
      simp only [List.filter_cons, List.filter_nil, H.hk, Kind.isSolid, hcxL, Bool.false_or]
      split_ifs <;> simp_all
    rw [hRc]
    by_cases hE : c₀.endB.isLeft = true
    · obtain ⟨hs', hy⟩ := hBL hE
      rw [if_pos (by simp [hs', hy])]
      rcases hsh with rfl | rfl <;> simp [mkC, Kind.isSolid, hxL, hcxL, hE]
    · simp only [Bool.not_eq_true] at hE
      rcases hsh with rfl | rfl <;> simp [mkC, Kind.isSolid, hxL, hcxL, hE]
  · intro _ h
    rcases hord with h' | h' <;> rw [h'] at h <;> simp at h
  · intro hl
    rcases hlab with h | h
    · exact absurd h hl
    · subst h
      refine ⟨(mkC (.G .plus) (newA 1) (newA 0)).labelQ (newA 0), hcs.mem_iff.2 ?_, ?_⟩
      · apply List.mem_append_left
        simp only [labW, labelQs]
        exact List.mem_map_of_mem (by simp)
      · simp [Comp.labelQ, mkC, Kind.isRandom]
  · have hx : (liftA 2 x).isRight = true := by simpa using hxR
    have a0 := sameMol_of_waved (g := ⟨cs, co⟩) (hcs.mem_iff.2 (List.mem_append_right _
      (List.mem_cons_self ..))) hx (isRight_newA 0)
    have a1 := sameMol_of_waved (g := ⟨cs, co⟩) (hcs.mem_iff.2 (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (isRight_newA 0) (isRight_newA 1)
    intro i
    fin_cases i
    · exact a0
    · exact (Graph.sameMol_equivalence _).trans a0 a1

end W2DTerms

section W2All

variable {k n : ℕ} {C : ℕ} {x : Atom k n} {Γ : Graph k n} {i : ℕ} {ℓ : Comp (Atom k n)}

private theorem WCtx.allTerms (H : WCtx C x Γ i ℓ) : ∀ T ∈ w2Out x Γ i, TermOK Γ x T := by
  have hx := H.right
  intro T hT
  unfold w2Out at hT
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  rcases hT with (((((rfl | rfl) | ⟨d, hd, rfl⟩) | ⟨d, hd, rfl⟩) | (rfl | rfl | rfl | rfl)) |
    ⟨d, hd, rfl⟩) | ⟨d, hd, rfl⟩
  · exact termSL hx _
  · exact H.termW2 _
  · refine H.termD1 hd none (Or.inl rfl) ?_ _
    simp only [labW, List.append_assoc]
    exact List.Perm.append_left d (List.perm_append_comm (l₁ := [_]) (l₂ := [_]))
  · refine H.termD2 hd none (Or.inl rfl) ?_ _
    simp only [labW, List.append_assoc]
    exact List.Perm.append_left d (List.perm_append_comm (l₁ := [_, _]) (l₂ := [_]))
  · exact termQx hx ⟨ℓ, H.mem, by simp [H.hk, Kind.isRandom]⟩ _
  · exact H.termQ2 _
  · exact H.termQ3 _
  · exact H.termQ4 _
  · exact H.termD1 hd (some (liftA 1 x)) (Or.inr rfl) (List.Perm.refl _) _
  · exact H.termD2 hd (some (newA 0)) (Or.inr rfl) (List.Perm.refl _) _

/-- The light weights of charge `plus` or `minus` on `x`. -/
def HasLight (Γ : Graph k n) (x : Atom k n) : Prop :=
  ∃ c ∈ Γ.comps, (c.kind = .light .plus ∨ c.kind = .light .minus) ∧ c.x = x

/-- The terms of `O^{(x),2}_weight` at a graph with a light weight on `x`. -/
theorem oWeight2T_terms (hN : Γ.Normal C) (hP : Γ.Plain) (hL : Γ.LabelFree)
    (hK : Γ.RandomFirstInt) (hx : x.isRight = true) (hl : HasLight Γ x) :
    ∀ T ∈ oWeight2T x Γ, TermOK Γ x T := by
  have hpl : (!Γ.comps.all Comp.isPlainB) = false := by simp [all_isPlainB hL hP]
  unfold oWeight2T
  rw [ite_eq_right (by simp [hpl])]
  cases h : Γ.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) with
  | some i =>
    rw [oWeight2Pos_eq h]
    obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact WCtx.allTerms ⟨hN, hP, hL, hK, hx, by simp [hi], hp.1, hp.2⟩
  | none =>
    rw [oWeight2Pos_none h]
    simp only
    cases h' : Γ.conj.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) with
    | some i =>
      rw [oWeight2Pos_eq h']
      obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h'
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      have H : WCtx C x Γ.conj i Γ.conj.comps[i] :=
        ⟨Graph.conj_Normal hN, Graph.conj_Plain hP, Graph.conj_labelFree' hL,
          Graph.conj_randomFirstInt hK, hx, by simp [hi], hp.1, hp.2⟩
      intro T hT
      obtain ⟨T₀, hT₀, rfl⟩ := List.mem_map.1 hT
      exact (H.allTerms T₀ hT₀).conj
    | none =>
      exfalso
      obtain ⟨c, hc, hk, hcx⟩ := hl
      rw [List.findIdx?_eq_none_iff] at h h'
      rcases hk with hk | hk
      · have := h c hc
        simp [hk, hcx] at this
      · have := h' c.conj (List.mem_map_of_mem hc)
        simp [hk, hcx, Kind.conj, Charge.flip] at this

/-- `O^{(x),2}_weight` is the identity on a graph without light weight on `x`. -/
theorem oWeight2T_self (hl : ¬ HasLight Γ x) : oWeight2T x Γ = [Tracked.self Γ] := by
  unfold oWeight2T
  split_ifs with hpl
  · rfl
  have h : Γ.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro c hc
    by_contra hb
    simp only [Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at hb
    exact hl ⟨c, hc, Or.inl hb.1, hb.2⟩
  have h' : Γ.conj.comps.findIdx? (fun c => c.kind == .light .plus && c.x == x) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro c hc
    by_contra hb
    simp only [Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at hb
    obtain ⟨d, hd, rfl⟩ := Graph.mem_conj_comps.1 hc
    refine hl ⟨d, hd, Or.inr ?_, hb.2⟩
    have := hb.1
    rw [Comp.conj_kind] at this
    revert this
    rcases d with ⟨κ, a, b, m, l⟩
    cases κ <;> (try cases ‹Charge›) <;> (try cases ‹Wave›) <;> simp [Kind.conj, Charge.flip]
  rw [oWeight2Pos_none h]
  simp only
  rw [oWeight2Pos_none h']

end W2All

/-! ## The splitting of the regular weights -/

section O1Split

variable {V : Type*} [DecidableEq V]

/-- An unlabelled regular weight on `y`. -/
def IsRegU (y : V) (c : Comp V) : Prop :=
  (∃ ch, c.kind = .weight ch) ∧ c.x = y ∧ c.label = none

/-- The light weight of the charge of a regular weight. -/
def Comp.toLight (c : Comp V) : Comp V :=
  match c.kind with
  | .weight ch => { c with kind := .light ch }
  | _ => c

private theorem splitRegular_spec (y : V) : ∀ (cs : List (Comp V)), ∀ p ∈ splitRegular y cs,
    ∃ K R L : List (Comp V), cs.Perm (K ++ R) ∧ p.1.Perm (K ++ L.map Comp.toLight) ∧
      L.Sublist R ∧ (∀ c ∈ R, IsRegU y c) ∧ (∀ c ∈ K, ¬ IsRegU y c)
  | [] => by
    intro p hp
    simp only [splitRegular, List.mem_singleton] at hp
    subst hp
    exact ⟨[], [], [], by simp, by simp, by simp, by simp, by simp⟩
  | c :: cs => by
    intro p hp
    have ih := splitRegular_spec y cs
    by_cases hc : IsRegU y c
    · obtain ⟨⟨ch, hk⟩, hx, hl⟩ := hc
      have hsplit : splitRegular y (c :: cs) =
          (splitRegular y cs).map (fun p => (p.1, mOf ch * p.2)) ++
            (splitRegular y cs).map (fun p => ({ c with kind := .light ch } :: p.1, p.2)) := by
        simp [splitRegular, hk, hx, hl]
      have hR' : ∀ R : List (Comp V), (∀ d ∈ R, IsRegU y d) → ∀ d ∈ c :: R, IsRegU y d := by
        intro R hR d hd
        rcases List.mem_cons.1 hd with rfl | hd
        · exact ⟨⟨ch, hk⟩, hx, hl⟩
        · exact hR d hd
      rw [hsplit, List.mem_append, List.mem_map, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · obtain ⟨K, R, L, h1, h2, h3, h4, h5⟩ := ih q hq
        exact ⟨K, c :: R, L, (h1.cons c).trans List.perm_middle.symm, h2, h3.cons c,
          hR' R h4, h5⟩
      · obtain ⟨K, R, L, h1, h2, h3, h4, h5⟩ := ih q hq
        have hl' : c.toLight = { c with kind := .light ch } := by simp [Comp.toLight, hk]
        refine ⟨K, c :: R, c :: L, (h1.cons c).trans List.perm_middle.symm, ?_, h3.cons₂ c,
          hR' R h4, h5⟩
        simp only [List.map_cons, hl']
        exact (h2.cons _).trans List.perm_middle.symm
    · have hsplit : splitRegular y (c :: cs) = (splitRegular y cs).map (fun p => (c :: p.1, p.2)) := by
        simp only [splitRegular]
        split
        · rename_i ch hk
          rw [if_neg]
          rintro ⟨h1, h2⟩
          exact hc ⟨⟨ch, hk⟩, h1, by simpa using h2⟩
        · rfl
      rw [hsplit, List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      obtain ⟨K, R, L, h1, h2, h3, h4, h5⟩ := ih q hq
      refine ⟨c :: K, R, L, h1.cons c, h2.cons c, h3, h4, fun d hd => ?_⟩
      rcases List.mem_cons.1 hd with rfl | hd
      · exact hc
      · exact h5 d hd

end O1Split

section O1Graph

variable {k n : ℕ}

theorem Comp.map_liftA_zero (c : Comp (Atom k n)) : c.map (liftA 0) = c := by
  rw [liftA_zero_eq]; exact comp_map_id' c

theorem labF_none {V : Type*} (c : Comp V) : labF none c = c := rfl

/-- The outputs of `O^{(y),1}_weight`: the unlabelled regular weights `R` on `y` are removed, those
of the sublist `L` come back as light weights. -/
theorem oWeight1T_spec {y : Atom k n} {h : Graph k n} {t : Tracked k n}
    (ht : t ∈ oWeight1T y h) :
    ∃ (R : List (Comp (Atom k n))) (N : List (Comp (Atom k (n + 0)))) (h' : Graph k n),
      t = ⟨n, h', id⟩ ∧ Sch h 0 R N none h' ∧ N.length ≤ R.length ∧
      (∀ c ∈ N, ∃ c₀ ∈ R, c = c₀.toLight) ∧ (∀ c ∈ R, IsRegU y c) ∧
      (∀ c ∈ h.comps, IsRegU y c → c ∈ R) := by
  unfold oWeight1T at ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  obtain ⟨K, R, L, h1, h2, h3, h4, h5⟩ := splitRegular_spec y h.comps p hp
  refine ⟨R, L.map Comp.toLight, ⟨p.1, p.2 * h.coeff⟩, rfl, ⟨fun c hc => ?_, K, h1, ?_⟩,
    by simpa using h3.length_le, fun c hc => ?_, h4, ?_⟩
  · obtain ⟨⟨ch, hk⟩, -, -⟩ := h4 c hc
    simp [hk, Kind.isRandom]
  · refine h2.trans (List.Perm.of_eq ?_)
    simp [labF, liftCs_zero]
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    exact ⟨c₀, h3.subset hc₀, rfl⟩
  · intro c hc hr
    rcases List.mem_append.1 (h1.mem_iff.1 hc) with hK | hR
    · exact absurd hr (h5 c hK)
    · exact hR

theorem Sch.mem_of_notR {Γ : Graph k n} {j : ℕ} {R : List (Comp (Atom k n))}
    {N : List (Comp (Atom k (n + j)))} {lab : Option (Atom k (n + j))} {g : Graph k (n + j)}
    (hS : Sch Γ j R N lab g) {c₀ : Comp (Atom k n)} (hc₀ : c₀ ∈ Γ.comps) (hn : c₀ ∉ R) :
    labF lab (c₀.map (liftA j)) ∈ g.comps := by
  obtain ⟨-, K, h1, h2⟩ := hS
  have hK : c₀ ∈ K := by
    rcases List.mem_append.1 (h1.mem_iff.1 hc₀) with h | h
    · exact h
    · exact absurd h hn
  exact h2.mem_iff.2 (List.mem_map.2 ⟨c₀.map (liftA j), List.mem_append_left _
    (mem_liftCs.2 ⟨c₀, hK, rfl⟩), rfl⟩)

/-- An atom with a component other than a `×`-dotted edge, a solid edge or `s` is not standard
neutral. -/
private theorem std_false_of_other {m : ℕ} {g : Graph k m} {u : Atom k m} {c : Comp (Atom k m)}
    (hc : c ∈ g.comps) (h1 : c.kind ≠ .xdot) (h2 : c.kind.isSolid = false)
    (h3 : c.kind ≠ .waved .s) (hu : c.x = u ∨ c.y = u) :
    g.stdNeutralAt u = false := by
  unfold Graph.stdNeutralAt
  simp only
  set cs := g.comps.filter fun c => c.kind != .xdot && (c.x == u || c.y == u) with hcs
  have hmem : c ∈ cs := List.mem_filter.2 ⟨hc, by
    rcases hu with hu | hu <;> simp [h1, hu]⟩
  have e1 := List.length_eq_length_filter_add (l := cs) (fun d => d.kind.isSolid)
  have e2 := List.length_eq_length_filter_add (l := cs.filter fun d => !d.kind.isSolid)
    (fun d => d.kind == .waved .s)
  have hs : ((cs.filter fun d => !d.kind.isSolid).filter fun d => d.kind == .waved .s) =
      cs.filter fun d => d.kind == .waved .s := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro d _
    by_cases hd : d.kind = .waved .s
    · simp [hd, Kind.isSolid]
    · simp [hd]
  have hother : 0 < ((cs.filter fun d => !d.kind.isSolid).filter
      fun d => !(d.kind == .waved .s)).length :=
    List.length_pos_of_mem (List.mem_filter.2 ⟨List.mem_filter.2 ⟨hmem, by simp [h2]⟩,
      by simp [h3]⟩)
  rw [hs] at e2
  by_contra hne
  simp only [Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at hne
  omega

private theorem ordL_eq_length {V : Type*} (L : List (Comp V)) (h : ∀ c ∈ L, c.kind.ord = 1) :
    ordL L = L.length := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    rw [ordL_cons, h c (List.mem_cons_self ..), ih (fun d hd => h d (List.mem_cons_of_mem _ hd))]
    simp; ring

private theorem Kind.isWeight_of_molT (κ : Kind)
    (h : κ.joinsMol = true ∧ κ ≠ .dot ∨ κ.isDiffusive = true) : κ.isWeight = false := by
  cases κ <;> simp_all [Kind.joinsMol, Kind.isDiffusive, Kind.isWeight]

private theorem Kind.isWeight_of_solid (κ : Kind) (h : κ.isSolid = true) : κ.isWeight = false := by
  cases κ <;> simp_all [Kind.isSolid, Kind.isWeight]

/-- The quantities of the descent under `O^{(y),1}_weight`. -/
theorem o1_facts {y : Atom k n} {h : Graph k n} (hP : h.Plain) (hK : h.RandomFirstInt)
    {R : List (Comp (Atom k n))} {N : List (Comp (Atom k (n + 0)))} {h' : Graph k n}
    (hS : Sch h 0 R N none h') (hNl : N.length ≤ R.length)
    (hNR : ∀ c ∈ N, ∃ c₀ ∈ R, c = c₀.toLight) (hR : ∀ c ∈ R, IsRegU y c) :
    h'.dotExcess = h.dotExcess ∧ h'.obl = h.obl + N.length ∧ h'.mfl = h.mfl ∧
      h'.eextN = h.eextN ∧ h'.phi + R.length ≤ h.phi + 1000 * N.length ∧ h'.Plain ∧
      h'.RandomFirstInt ∧ (h.XdotApart → h'.XdotApart) ∧ (h.LabelFree → h'.LabelFree) ∧
      (∀ u v, h.SameMol u v → h'.SameMol u v) ∧ (∀ C, h.Normal C → h'.Normal C) := by
  have hRm : ∀ c ∈ R, c ∈ h.comps := by
    obtain ⟨-, K, h1, -⟩ := hS
    exact fun c hc => h1.mem_iff.2 (List.mem_append_right _ hc)
  have hRw : ∀ c ∈ R, ∃ ch, c.kind = .weight ch := fun c hc => (hR c hc).1
  have hRy : ∀ c ∈ R, c.x = y ∧ c.y = y := by
    intro c hc
    obtain ⟨⟨ch, hk⟩, hx, -⟩ := hR c hc
    have := (hP c (hRm c hc)).2.2.2.2.1 (by rw [hk]; rfl)
    exact ⟨hx, this.trans hx⟩
  have hyR : R ≠ [] → y.isRight = true := by
    intro hne
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil R hne
    obtain ⟨ch, hk⟩ := hRw c hc
    rw [← (hRy c hc).1]
    exact hK c (hRm c hc) (by simp [hk, Kind.isRandom])
  have hNs : ∀ c ∈ N, (∃ ch, c.kind = .light ch) ∧ c.x = y ∧ c.y = y ∧
      c.label = none ∧ NewOK c := by
    intro c hc
    obtain ⟨c₀, hc₀R, rfl⟩ := hNR c hc
    obtain ⟨⟨ch, hk⟩, hx, hl⟩ := hR c₀ hc₀R
    obtain ⟨hx', hy'⟩ := hRy c₀ hc₀R
    have hmi := (hP c₀ (hRm c₀ hc₀R)).1
    have e : c₀.toLight = { c₀ with kind := .light ch } := by simp [Comp.toLight, hk]
    rw [e]
    refine ⟨⟨ch, rfl⟩, hx', hy', hl, hmi, Or.inr (Or.inr (Or.inl ⟨ch, rfl⟩)),
      fun _ => by simp [hx', hy'], fun h => by simp [Kind.isSolid] at h, fun h => ?_⟩
    simp [hl] at h
  have hNd : ∀ c ∈ N, c.kind ≠ .dot ∧ c.kind ≠ .xdot := by
    intro c hc
    obtain ⟨⟨ch, hk⟩, -⟩ := hNs c hc
    rw [hk]; exact ⟨by simp, by simp⟩
  have hexc : h'.dotExcess = h.dotExcess := hS.dotExcess (fun c hc => (hNd c hc).1)
  have hord := hS.ord
  have hoR : ordL R = 0 := by
    have : ∀ c ∈ R, c.kind.ord = 0 := fun c hc => by
      obtain ⟨ch, hk⟩ := hRw c hc; rw [hk]; rfl
    unfold ordL
    rw [List.sum_eq_zero]
    intro a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    exact this c hc
  have hoN : ordL N = N.length := ordL_eq_length N fun c hc => by
    obtain ⟨⟨ch, hk⟩, -⟩ := hNs c hc; rw [hk]; rfl
  have hdeg : ∀ u : Atom k n, h'.deg u = h.deg u := by
    intro u
    have := hS.deg u
    have e1 : (R.filter fun c => c.kind.isSolid && atB u c) = [] :=
      List.filter_eq_nil_iff.2 fun c hc => by
        obtain ⟨ch, hk⟩ := hRw c hc; simp [hk, Kind.isSolid]
    have e2 : (N.filter fun c => c.kind.isSolid && atB (liftA 0 u) c) = [] :=
      List.filter_eq_nil_iff.2 fun c hc => by
        obtain ⟨⟨ch, hk⟩, -⟩ := hNs c hc; simp [hk, Kind.isSolid]
    rw [e1, e2, liftA_zero] at this
    simpa using this
  have hlw := hS.lwN
  have hrw := hS.rwN
  have hltR : (R.filter fun c => c.kind.isLt).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc; obtain ⟨ch, hk⟩ := hRw c hc; simp [hk, Kind.isLt]
  have hrgR : (R.filter fun c => c.kind.isRg).length = R.length := by
    rw [List.filter_eq_self.2]
    intro c hc; obtain ⟨ch, hk⟩ := hRw c hc; simp [hk, Kind.isRg]
  have hltN : (N.filter fun c => c.kind.isLt).length = N.length := by
    rw [List.filter_eq_self.2]
    intro c hc; obtain ⟨⟨ch, hk⟩, -⟩ := hNs c hc; simp [hk, Kind.isLt]
  have hrgN : (N.filter fun c => c.kind.isRg).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc; obtain ⟨⟨ch, hk⟩, -⟩ := hNs c hc; simp [hk, Kind.isRg]
  have hdX : h'.degX = h.degX := by
    unfold Graph.degX
    exact Finset.sum_congr rfl fun i _ => by rw [hdeg]
  have hbad : h'.badN ≤ h.badN := by
    rw [badN_eq, badN_eq]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hiy : (.inr i : Atom k n) = y
    · by_cases hRe : R = []
      · subst hRe
        have hL0 : N = [] := List.eq_nil_of_length_eq_zero (by simpa using hNl)
        subst hL0
        have hu := hS.local_untouched (u := .inr i) (by simp) (by simp)
        simp only [liftA_zero] at hu
        simp only [badI, hu.1, hu.2]
        exact le_refl _
      · obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil R hRe
        obtain ⟨ch, hk⟩ := hRw c hc
        have hstd : h.stdNeutralAt (.inr i) = false :=
          std_false_of_other (hRm c hc) (by rw [hk]; simp) (by rw [hk]; rfl) (by rw [hk]; simp)
            (Or.inl ((hRy c hc).1.trans hiy.symm))
        simp only [badI, hstd, hdeg]
        split_ifs <;> simp_all
    · have hu := hS.local_untouched (u := .inr i)
        (fun c hc => by
          have := hRy c hc
          simp [atB, this.1, this.2, Ne.symm hiy])
        (fun c hc => by
          obtain ⟨-, h1, h2, -⟩ := hNs c hc
          simp [atB, h1, h2, liftA_zero, Ne.symm hiy])
      simp only [liftA_zero] at hu
      simp only [badI, hu.1, hu.2]
      exact le_refl _
  refine ⟨hexc, ?_, Graph.mfl_eq_of_iff (hS.sepInt_iff fun c hc => (hNd c hc).1), ?_, ?_,
    hS.plain hP fun c hc => (hNs c hc).2.2.2.2, hS.randomFirstInt hK fun c hc _ => ?_,
    fun hX => hS.xdotApart (fun c hc => hNd c hc) hX,
    fun hL => hS.labelFree hL fun c hc => (hNs c hc).2.2.2.1,
    fun u v huv => by simpa [liftA_zero] using hS.sameMol huv, fun C hN => ?_⟩
  · simp only [Graph.obl, hexc]
    rw [hoR, hoN] at hord
    push_cast at hord ⊢
    linarith
  · have := hS.eextN
    have e1 : (R.filter fun c => c.kind.isSolid && (c.x.isLeft || c.y.isLeft)) = [] :=
      List.filter_eq_nil_iff.2 fun c hc => by
        obtain ⟨ch, hk⟩ := hRw c hc; simp [hk, Kind.isSolid]
    have e2 : (N.filter fun c =>
        c.kind.isSolid && (c.x.isLeft || c.y.isLeft)) = [] :=
      List.filter_eq_nil_iff.2 fun c hc => by
        obtain ⟨⟨ch, hk⟩, -⟩ := hNs c hc; simp [hk, Kind.isSolid]
    rw [e1, e2] at this
    simpa using this
  · unfold Graph.phi
    omega
  · obtain ⟨-, h1, -, -⟩ := hNs c hc
    rw [h1]
    have hne : R ≠ [] := by
      intro hR0
      subst hR0
      obtain ⟨c₀, hc₀, -⟩ := hNR c hc
      simp at hc₀
    exact hyR hne
  · -- normal regular
    obtain ⟨⟨hsz, hcon, hint, hnoint⟩, hsol, hxs⟩ := hN
    have hnR : ∀ c ∈ h.comps, (c.kind.isWeight = false) → c ∉ R := by
      intro c _ hw hcR
      obtain ⟨ch, hk⟩ := hRw c hcR
      rw [hk] at hw; cases hw
    have hmem : ∀ c ∈ h.comps, c.kind.isWeight = false → c ∈ h'.comps := by
      intro c hc hw
      have := hS.mem_of_notR hc (hnR c hc hw)
      simpa [labF_none, Comp.map_liftA_zero] using this
    have hback : ∀ c ∈ h'.comps, c.kind.isWeight = false → c ∈ h.comps := by
      intro c hc hw
      rcases hS.mem_cases hc with ⟨c₀, hc₀, rfl⟩ | ⟨c₁, hc₁, rfl⟩
      · simpa [labF_none, Comp.map_liftA_zero] using hc₀
      · obtain ⟨⟨ch, hk⟩, -⟩ := hNs _ hc₁
        simp [labF_none, hk, Kind.isWeight] at hw
    have hloop : ∀ c ∈ h'.comps, c.kind.isWeight = true → c.x = c.y := by
      intro c hc hw
      exact ((hS.plain hP fun c hc => (hNs c hc).2.2.2.2) c hc).2.2.2.2.1 hw |>.symm
    have hlen : h'.comps.length ≤ h.comps.length := by
      obtain ⟨-, K, h1, h2⟩ := hS
      rw [h2.length_eq, h1.length_eq]
      simp only [List.length_map, List.length_append, liftCs, List.length_map]
      omega
    refine ⟨⟨by omega, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro u v
      refine reach_map (G := h.edgeGraph) (H := h'.edgeGraph) id
        (fun a b hab => SimpleGraph.Adj.reachable ?_) (hcon u v)
      show h'.edgeGraph.Adj a b
      rw [Graph.edgeGraph, SimpleGraph.fromRel_adj] at hab ⊢
      refine ⟨hab.1, ?_⟩
      rcases hab.2 with ⟨c, hc, h1, h2⟩ | ⟨c, hc, h1, h2⟩
      · have hw : c.kind.isWeight = false := by
          by_contra hw
          simp only [Bool.not_eq_false] at hw
          exact hab.1 (h1 ▸ h2 ▸ ((hP c hc).2.2.2.2.1 hw).symm)
        exact Or.inl ⟨c, hmem c hc hw, h1, h2⟩
      · have hw : c.kind.isWeight = false := by
          by_contra hw
          simp only [Bool.not_eq_false] at hw
          exact hab.1 (h1 ▸ h2 ▸ ((hP c hc).2.2.2.2.1 hw))
        exact Or.inr ⟨c, hmem c hc hw, h1, h2⟩
    · intro a b
      refine reach_map (G := h.wavedThetaGraph) (H := h'.wavedThetaGraph) id
        (fun u v huv => SimpleGraph.Adj.reachable ?_) (hint a b)
      show h'.wavedThetaGraph.Adj u v
      rw [Graph.wavedThetaGraph, SimpleGraph.fromRel_adj] at huv ⊢
      refine ⟨huv.1, ?_⟩
      have hw : ∀ c : Comp (Atom k n), (c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨
          c.kind.isDiffusive = true) → c.kind.isWeight = false :=
        fun c hc => Kind.isWeight_of_molT _ hc
      rcases huv.2 with ⟨c, hc, h1, h2⟩ | ⟨c, hc, h1, h2⟩
      · exact Or.inl ⟨c, hmem c hc (hw c h1), h1, h2⟩
      · exact Or.inr ⟨c, hmem c hc (hw c h1), h1, h2⟩
    · intro c hc hk
      exact hnoint c (hback c hc (by rw [hk]; rfl)) hk
    · intro c hc hk
      exact hsol c (hback c hc (Kind.isWeight_of_solid _ hk)) hk
    · intro u v huv
      have key : ∀ (Q : Kind → Prop), (∀ κ, Q κ → κ.isWeight = false) →
          ((∃ c ∈ h'.comps, Q c.kind ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) ↔
            (∃ c ∈ h.comps, Q c.kind ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u))) := by
        intro Q hQ
        constructor
        · rintro ⟨c, hc, hq, hm⟩; exact ⟨c, hback c hc (hQ _ hq), hq, hm⟩
        · rintro ⟨c, hc, hq, hm⟩; exact ⟨c, hmem c hc (hQ _ hq), hq, hm⟩
      rw [key (fun κ => κ = .xdot) (fun κ h => by rw [h]; rfl),
        key (fun κ => κ.isSolid = true) (fun κ h => Kind.isWeight_of_solid _ h)]
      exact hxs u v huv

end O1Graph

/-! ## The step of the weight expansion -/

section WStep

variable {k n : ℕ}

private theorem LexLt.of_le_right {m m' : ℕ} {t : Graph k m'} {g Γ : Graph k m} (h : LexLt t g)
    (h1 : g.mfl = Γ.mfl) (h2 : g.eextN = Γ.eextN) (h3 : g.phi ≤ Γ.phi) : LexLt t Γ := by
  unfold LexLt at h ⊢
  omega

private theorem LexLt.of_le_left {m m' : ℕ} {t t' : Graph k m'} {Γ : Graph k m} (h : LexLt t Γ)
    (h1 : t'.mfl = t.mfl) (h2 : t'.eextN = t.eextN) (h3 : t'.phi ≤ t.phi) : LexLt t' Γ := by
  unfold LexLt at h ⊢
  omega

/-- `O^{(y),1}_weight` applied to the output of a step. -/
private theorem StepOut.o1 {Γ : Graph k n} {t : Tracked k n} (hS : StepOut Γ t) {y : Atom k t.nOut}
    {t₄ : Tracked k t.nOut} (ht₄ : t₄ ∈ oWeight1T y t.g) :
    StepOut Γ ⟨t₄.nOut, t₄.g, t₄.f ∘ t.f⟩ := by
  obtain ⟨R, N, h', rfl, hSch, hNl, hNR, hR, -⟩ := oWeight1T_spec ht₄
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := hS
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, -⟩ := o1_facts e6 e5 hSch hNl hNR hR
  have hLF : h'.LabelFree → t.g.LabelFree := by
    intro hL c hc
    by_cases hcR : c ∈ R
    · exact (hR c hcR).2.2
    · have := hL _ (hSch.mem_of_notR hc hcR)
      simpa [labF_none, Comp.map_liftA_zero] using this
  refine ⟨by rw [f1]; exact e1, by rw [f2]; omega, fun hl he => ?_, f8 e4, f7, f6, ?_,
    fun u v huv => f10 _ _ (e8 u v huv), fun u' => ?_⟩
  · have hN0 : N.length = 0 := by
      change h'.obl = Γ.obl at he
      omega
    have ht0 : t.g.obl = Γ.obl := by
      change h'.obl = Γ.obl at he
      omega
    exact LexLt.of_le_left (t' := h') (e3 (hLF hl) ht0) f3 f4 (by omega)
  · rcases e7 with hL | hQ
    · exact Or.inl (f9 hL)
    · right
      have hR0 : R = [] := by
        apply List.eq_nil_iff_forall_not_mem.2
        intro c hc
        obtain ⟨u, -, hall⟩ := hQ
        obtain ⟨⟨ch, hk⟩, -, hl⟩ := hR c hc
        have hcm : c ∈ t.g.comps := by
          obtain ⟨-, K, h1, -⟩ := hSch
          exact h1.mem_iff.2 (List.mem_append_right _ hc)
        have := hall c hcm (Or.inl (by simp [hk, Kind.isRandom]))
        rw [hl] at this
        cases this
      subst hR0
      have hN0 : N = [] := List.eq_nil_of_length_eq_zero (by simpa using hNl)
      subst hN0
      have hmem : ∀ c, c ∈ h'.comps ↔ c ∈ t.g.comps := by
        obtain ⟨-, K, h1, h2⟩ := hSch
        intro c
        rw [h2.mem_iff, h1.mem_iff]
        simp [labF, liftCs_zero]
      obtain ⟨u, ⟨c, hc, hl⟩, hall⟩ := hQ
      exact ⟨u, ⟨c, (hmem c).2 hc, hl⟩, fun d hd => hall d ((hmem d).1 hd)⟩
  · obtain ⟨u, hu⟩ := e9 u'
    exact ⟨u, f10 _ _ hu⟩

/-- A step relative to the output of `O^{(x),1}_weight` is a step relative to its input. -/
private theorem StepOut.of_o1 {Γ g₁ : Graph k n} {N : ℕ} (e1 : g₁.dotExcess = Γ.dotExcess)
    (e2 : g₁.obl = Γ.obl + N) (e3 : g₁.mfl = Γ.mfl) (e4 : g₁.eextN = Γ.eextN)
    (e5 : N = 0 → g₁.phi ≤ Γ.phi) (e6 : ∀ u v, Γ.SameMol u v → g₁.SameMol u v)
    {t : Tracked k n} (hS : StepOut g₁ t) : StepOut Γ t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hS
  refine ⟨by rw [← e1]; exact h1, by omega, fun hl he => ?_, h4, h5, h6, h7,
    fun u v huv => h8 u v (e6 u v huv), h9⟩
  have hN : N = 0 := by omega
  exact LexLt.of_le_right (h3 hl (by omega)) e3 e4 (e5 hN)

/-- The step of the weight expansion at `x`: every output has the clauses `StepOut`. -/
theorem oWeightT_step {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C) (hP : Γ.Plain)
    (hL : Γ.LabelFree) (hK : Γ.RandomFirstInt) (hX : Γ.XdotApart) (hx : x.isRight = true)
    (hw : 0 < Γ.wt x) : ∀ t ∈ oWeightT x Γ, StepOut Γ t := by
  obtain ⟨cw, hcw, hkw, hcwx⟩ : ∃ c ∈ Γ.comps, ((∃ ch, c.kind = .weight ch) ∨
      (∃ ch, c.kind = .light ch)) ∧ c.x = x := by
    unfold Graph.wt at hw
    obtain ⟨c, hc⟩ := List.exists_mem_of_length_pos hw
    rw [List.mem_filter] at hc
    refine ⟨c, hc.1, ?_⟩
    have h2 := hc.2
    rcases hkk : c.kind with _ | ch | ch | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
      rw [hkk] at h2 <;> simp at h2
    · exact ⟨Or.inl ⟨ch, rfl⟩, h2⟩
    · exact ⟨Or.inr ⟨ch, rfl⟩, h2⟩
  intro t ht
  unfold oWeightT at ht
  split_ifs at ht with hany
  swap
  · exfalso
    apply hany
    refine List.any_eq_true.2 ⟨cw, hcw, ?_⟩
    rcases hkw with ⟨ch, hk⟩ | ⟨ch, hk⟩ <;> simp [hk, hcwx]
  simp only [TExpansion.bind, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨u₃, ⟨u₂, ⟨t₁, ht₁, t₂, ht₂, rfl⟩, t₃, ht₃, rfl⟩, t₄, ht₄, rfl⟩ := ht
  obtain ⟨R, N, g₁, rfl, hSch, hNl, hNR, hR, hall⟩ := oWeight1T_spec ht₁
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := o1_facts hP hK hSch hNl hNR hR
  have hN₁ := f11 C hN
  simp only [Function.comp_id] at ht₂ ht₃ ht₄ ⊢
  by_cases hl : HasLight g₁ x
  · have hT := oWeight2T_terms hN₁ f6 (f9 hL) f7 hx hl t₂ ht₂
    have h3 := hT.step hN₁ f6 (f9 hL) f7 (f8 hX) ht₃
    have h4 := h3.o1 ht₄
    exact StepOut.of_o1 f1 f2 f3 f4 (fun h0 => by rw [h0] at f5; omega) f10 h4
  · change t₂ ∈ oWeight2T x g₁ at ht₂
    rw [oWeight2T_self hl, List.mem_singleton] at ht₂
    subst ht₂
    have hN0 : N = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro c hc
      obtain ⟨c₀, hc₀, rfl⟩ := hNR c hc
      obtain ⟨⟨ch, hk⟩, hcx, -⟩ := hR c₀ hc₀
      apply hl
      refine ⟨labF none c₀.toLight, hSch.mem_N hc, ?_, ?_⟩
      · cases ch <;> simp [labF, Comp.toLight, hk]
      · simp [labF, Comp.toLight, hk, hcx]
    subst hN0
    have hRne : R ≠ [] := by
      intro hR0
      subst hR0
      apply hl
      refine ⟨cw, ?_, ?_, hcwx⟩
      · have := hSch.mem_of_notR hcw (by simp)
        simpa [labF_none, Comp.map_liftA_zero] using this
      · rcases hkw with ⟨ch, hk⟩ | ⟨ch, hk⟩
        · exfalso
          have := hall cw hcw ⟨⟨ch, hk⟩, hcwx, hL cw hcw⟩
          simp at this
        · rw [hk]; cases ch <;> simp
    have hT : TermOK Γ x ⟨n, g₁, id⟩ := by
      rw [tracked_id_eq]
      refine ⟨0, R, [], none, g₁, 0, rfl, hSch, by simp, by simp, ?_, fun i => i.elim0,
        by simp, by simp, fun h => by simp, by simp, ?_, fun h => absurd rfl h, fun i => i.elim0⟩
      · have hoR : ordL R = 0 := by
          unfold ordL
          rw [List.sum_eq_zero]
          intro a ha
          obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
          obtain ⟨⟨ch, hk⟩, -⟩ := hR c hc
          rw [hk]; rfl
        simp [hoR]
      · intro _ _
        have : 1 ≤ R.length := List.length_pos_of_ne_nil hRne
        simp only [List.length_nil, mul_zero, add_zero] at f5
        simp only [ite_true]
        omega
    have h3 := hT.step hN hP hL hK hX ht₃
    exact h3.o1 ht₄

end WStep


/-! ## `O_dot` on the graph with every solid edge reversed -/

private theorem isPlainB_swapSolid {V : Type*} (c : Comp V) : c.swapSolid.isPlainB = c.isPlainB := by
  unfold Comp.swapSolid
  split <;> rfl

section Corr

open List

/-- Two components of the same kind, minor and label whose ends are equal, or exchanged when they
are not weights. -/
private def URel {V : Type*} (c' c : Comp V) : Prop :=
  c'.kind = c.kind ∧ c'.minor = c.minor ∧ c'.label = c.label ∧
    ((c'.x = c.x ∧ c'.y = c.y) ∨ (c.kind.isWeight = false ∧ c'.x = c.y ∧ c'.y = c.x))

/-- Two components of the same kind, minor and label whose ends are equal or exchanged, or which
are weights. -/
def ORel {V : Type*} (c' c : Comp V) : Prop :=
  c'.kind = c.kind ∧ c'.minor = c.minor ∧ c'.label = c.label ∧
    (c.kind.isWeight = true ∨ (c'.x = c.x ∧ c'.y = c.y) ∨ (c'.x = c.y ∧ c'.y = c.x))

private theorem URel.oRel {V : Type*} {c' c : Comp V} (h : URel c' c) : ORel c' c := by
  obtain ⟨h1, h2, h3, h4 | ⟨-, h4⟩⟩ := h
  · exact ⟨h1, h2, h3, Or.inr (Or.inl h4)⟩
  · exact ⟨h1, h2, h3, Or.inr (Or.inr h4)⟩

private theorem oRel_refl {V : Type*} (c : Comp V) : ORel c c :=
  ⟨rfl, rfl, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

private theorem uRel_swapSolid {V : Type*} (c : Comp V) : URel c.swapSolid c := by
  rcases c with ⟨κ, x, y, m, l⟩
  cases κ <;> simp [URel, Comp.swapSolid, Kind.isSolid, Kind.isWeight]

private theorem oRel_swapSolid_right {V : Type*} (c : Comp V) : ORel c c.swapSolid := by
  rcases c with ⟨κ, x, y, m, l⟩
  cases κ <;> simp [ORel, Comp.swapSolid, Kind.isSolid, Kind.isWeight]

private theorem forall₂_swapSolid {V : Type*} (l : List (Comp V)) :
    Forall₂ URel (l.map Comp.swapSolid) l := by
  rw [forall₂_map_left_iff, forall₂_same]
  exact fun c _ => uRel_swapSolid c

/-- Two tracked graphs with the same number of atoms and the same atom map, the same coefficient
and corresponding components. -/
def TRel {k n : ℕ} (t' t : Tracked k n) : Prop :=
  ∃ (m : ℕ) (g' g : Graph k m) (f : Atom k n → Atom k m), t' = ⟨m, g', f⟩ ∧ t = ⟨m, g, f⟩ ∧
    g'.coeff = g.coeff ∧ Forall₂ ORel g'.comps g.comps

/-! ### Lists of corresponding entries -/

private theorem forall₂_any {α β : Type*} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ a b, R a b → p a = q b) {l' : List α} {l : List β} (h : Forall₂ R l' l) :
    l'.any p = l.any q := by
  induction h with
  | nil => rfl
  | cons h₁ _ ih => simp only [List.any_cons, hpq _ _ h₁, ih]

private theorem forall₂_filterMap_eq {α β γ : Type*} {R : α → β → Prop} {f : α → Option γ}
    {g : β → Option γ} (hfg : ∀ a b, R a b → f a = g b) {l' : List α} {l : List β}
    (h : Forall₂ R l' l) : l'.filterMap f = l.filterMap g := by
  induction h with
  | nil => rfl
  | cons h₁ _ ih => simp only [List.filterMap_cons, hfg _ _ h₁, ih]

private theorem forall₂_mem_left {α β : Type*} {R : α → β → Prop} {l' : List α} {l : List β}
    (h : Forall₂ R l' l) : ∀ a ∈ l', ∃ b ∈ l, R a b := by
  induction h with
  | nil => intro a ha; simp at ha
  | cons h₁ _ ih =>
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self .., h₁⟩
    · obtain ⟨b, hb, hab⟩ := ih a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

private theorem forall₂_mem_right {α β : Type*} {R : α → β → Prop} {l' : List α} {l : List β}
    (h : Forall₂ R l' l) : ∀ b ∈ l, ∃ a ∈ l', R a b := by
  induction h with
  | nil => intro a ha; simp at ha
  | cons h₁ _ ih =>
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self .., h₁⟩
    · obtain ⟨a, ha, hab⟩ := ih b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

private theorem forall₂_imp_mem {α β : Type*} {R S : α → β → Prop} {l' : List α} {l : List β}
    (h : Forall₂ R l' l) (H : ∀ a b, a ∈ l' → b ∈ l → R a b → S a b) : Forall₂ S l' l := by
  induction h with
  | nil => exact .nil
  | cons h₁ _ ih =>
    exact .cons (H _ _ (List.mem_cons_self ..) (List.mem_cons_self ..) h₁)
      (ih fun a b ha hb => H a b (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb))

private theorem forall₂_isEmpty {α β : Type*} {R : α → β → Prop} {l' : List α} {l : List β}
    (h : Forall₂ R l' l) : l'.isEmpty = l.isEmpty := by
  cases h <;> rfl

/-- A sublist of a list without repetitions corresponds to the sublist at the same positions of a
corresponding list without repetitions. -/
private theorem sublist_transfer {α β : Type*} {R : α → β → Prop} {l' : List α} {l : List β}
    (h : Forall₂ R l' l) (hn' : l'.Nodup) (hn : l.Nodup) {A' : List α} (hA' : A' <+ l') :
    ∃ A, A <+ l ∧ Forall₂ R A' A ∧ Forall₂ (fun a' a => R a' a ∧ (a' ∈ A' ↔ a ∈ A)) l' l := by
  induction h generalizing A' with
  | nil =>
    rw [List.sublist_nil] at hA'
    subst hA'
    exact ⟨[], List.Sublist.slnil, .nil, .nil⟩
  | @cons a' a l' l h₁ h₂ ih =>
    rw [List.nodup_cons] at hn' hn
    cases hA' with
    | cons _ hA' =>
      obtain ⟨A, hA, hR, hM⟩ := ih hn'.2 hn.2 hA'
      refine ⟨A, hA.cons a, hR, .cons ⟨h₁, ?_⟩ hM⟩
      exact ⟨fun h => absurd (hA'.subset h) hn'.1, fun h => absurd (hA.subset h) hn.1⟩
    | cons_cons _ hA' =>
      obtain ⟨A, hA, hR, hM⟩ := ih hn'.2 hn.2 hA'
      refine ⟨a :: A, hA.cons_cons a, .cons h₁ hR, .cons ⟨h₁, by simp⟩ ?_⟩
      refine forall₂_imp_mem hM fun b' b hb' hb ⟨hr, hm⟩ => ⟨hr, ?_⟩
      have hb'a : b' ≠ a' := fun h => hn'.1 (h ▸ hb')
      have hba : b ≠ a := fun h => hn.1 (h ▸ hb)
      simp only [List.mem_cons, hb'a, hba, false_or, hm]

/-! ### The pairs of `O_dot` -/

variable {k n : ℕ}

/-- Two pairs of atoms that are equal as unordered pairs. -/
private def PRel (p' p : Atom k n × Atom k n) : Prop := p' = p ∨ p' = p.swap

/-- Two pairs of `O_dot` with the same flag that are equal as unordered pairs. -/
private def SPRel (p' p : Atom k n × Atom k n × Bool) : Prop :=
  p'.2.2 = p.2.2 ∧ PRel (p'.1, p'.2.1) (p.1, p.2.1)

private theorem bool_sym (a b c d : Bool) : (a && b || c && d) = (d && c || b && a) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem spJoined_comm (Γ : Graph k n) (p : Kind → Bool) (u v : Atom k n) :
    spJoined Γ p u v = spJoined Γ p v u := by
  unfold spJoined
  congr 1
  funext c
  rw [bool_sym (c.x == u), Bool.and_comm (c.x == v), Bool.and_comm (c.y == v)]

private theorem spJoined_rel {Γ' Γ : Graph k n} (hR : Forall₂ URel Γ'.comps Γ.comps)
    (p : Kind → Bool) (u v : Atom k n) : spJoined Γ' p u v = spJoined Γ p u v := by
  unfold spJoined
  refine forall₂_any (fun c' c h => ?_) hR
  obtain ⟨hk, -, -, ⟨hx, hy⟩ | ⟨-, hx, hy⟩⟩ := h
  · rw [hk, hx, hy]
  · rw [hk, hx, hy, bool_sym (c.y == u)]

private theorem pRel_iff (q' q p' p : Atom k n × Atom k n) (hq : PRel q' q) (hp : PRel p' p) :
    (q' == p' || q' == p'.swap) = (q == p || q == p.swap) := by
  rcases q with ⟨a, b⟩
  rcases p with ⟨c, d⟩
  apply Bool.eq_iff_iff.2
  rcases hq with rfl | rfl <;> rcases hp with rfl | rfl <;>
    simp only [Prod.swap_prod_mk, beq_iff_eq, Prod.mk.injEq, Bool.or_eq_true] <;>
    tauto

private theorem spUniq_rel {Γ' Γ : Graph k n} (hR : Forall₂ URel Γ'.comps Γ.comps) :
    Forall₂ PRel (spUniq Γ') (spUniq Γ) := by
  have hc : Forall₂ PRel (spCand Γ') (spCand Γ) := by
    refine List.rel_filterMap (fun c' c h => ?_) hR
    obtain ⟨hk, -, -, ⟨hx, hy⟩ | ⟨-, hx, hy⟩⟩ := h
    · rw [hk, hx, hy]
      split_ifs
      · exact .some (Or.inl rfl)
      · exact .none
    · rw [hk, hx, hy, bne_comm]
      split_ifs
      · exact .some (Or.inr rfl)
      · exact .none
  refine List.rel_foldl (fun acc' acc hacc p' p hp => ?_) Forall₂.nil hc
  unfold spStep
  rw [forall₂_any (fun q' q hq => pRel_iff q' q p' p hq hp) hacc]
  split_ifs
  · exact hacc
  · exact List.rel_append hacc (.cons hp .nil)

private theorem splitPairs_rel {Γ' Γ : Graph k n} (hR : Forall₂ URel Γ'.comps Γ.comps) :
    Forall₂ SPRel Γ'.splitPairs Γ.splitPairs := by
  rw [splitPairs_eq, splitPairs_eq]
  refine List.rel_filterMap (fun p' p hp => ?_) (spUniq_rel hR)
  have hj : ∀ pr : Kind → Bool, spJoined Γ' pr p'.1 p'.2 = spJoined Γ pr p.1 p.2 := by
    intro pr
    rw [spJoined_rel hR]
    rcases hp with rfl | rfl
    · rfl
    · exact spJoined_comm Γ pr _ _
  simp only [hj]
  split_ifs
  · exact .some ⟨rfl, hp⟩
  · exact .none

/-! ### The terms of `O_dot` -/

private theorem dotChoice_rel {Γ' Γ : Graph k n} (hc : Γ'.coeff = Γ.coeff)
    (hR : Forall₂ URel Γ'.comps Γ.comps) {SP' SP A' A : List (Atom k n × Atom k n × Bool)}
    (hSP : Forall₂ (fun p' p => SPRel p' p ∧ (p' ∈ A' ↔ p ∈ A)) SP' SP)
    (hA : Forall₂ SPRel A' A) :
    (Γ'.dotChoice SP' A').coeff = (Γ.dotChoice SP A).coeff ∧
      Forall₂ URel (Γ'.dotChoice SP' A').comps (Γ.dotChoice SP A).comps := by
  have hxo : ∀ u v : Atom k n,
      (SP'.any fun p => !p.2.2 && ((p.1 == u && p.2.1 == v) || (p.1 == v && p.2.1 == u))) =
        (SP.any fun p => !p.2.2 && ((p.1 == u && p.2.1 == v) || (p.1 == v && p.2.1 == u))) := by
    intro u v
    refine forall₂_any (fun p' p h => ?_) hSP
    obtain ⟨⟨hb, hq⟩, -⟩ := h
    rcases p' with ⟨a', b', c'⟩
    rcases p with ⟨a, b, c⟩
    simp only at hb hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hb]
    · rw [hb, bool_sym (b == u)]
  have hxs : ∀ u v : Atom k n,
      (SP.any fun p => !p.2.2 && ((p.1 == u && p.2.1 == v) || (p.1 == v && p.2.1 == u))) =
        (SP.any fun p => !p.2.2 && ((p.1 == v && p.2.1 == u) || (p.1 == u && p.2.1 == v))) := by
    intro u v
    congr 1
    funext p
    rw [Bool.or_comm]
  refine ⟨?_, ?_⟩
  · simp only [Graph.dotChoice, hc]
    congr 2
    refine Forall₂.length_eq (List.rel_filter (fun p' p h => ?_) hA)
    dsimp only
    rw [h.1]
  · simp only [Graph.dotChoice]
    refine List.rel_append (List.rel_filter (fun c' c h => ?_) hR)
      (List.rel_filterMap (fun p' p h => ?_) hSP)
    · dsimp only
      obtain ⟨hk, -, -, ⟨hx, hy⟩ | ⟨-, hx, hy⟩⟩ := h
      · rw [hk, hx, hy, hxo]
      · rw [hk, hx, hy, hxo, hxs]
    · obtain ⟨⟨hb, hq⟩, hm⟩ := h
      by_cases h1 : p ∈ A
      · have h1' : p' ∈ A' := hm.2 h1
        simp only [h1, h1', ↓reduceIte]
        refine .some ⟨rfl, rfl, rfl, ?_⟩
        rcases hq with h | h <;> simp only [Prod.mk.injEq, Prod.swap_prod_mk] at h <;>
          simp [mkC, h, Kind.isWeight]
      · have h1' : p' ∉ A' := fun h => h1 (hm.1 h)
        simp only [h1, h1', ↓reduceIte, hb]
        split_ifs
        · refine .some ⟨rfl, rfl, rfl, ?_⟩
          rcases hq with h | h <;> simp only [Prod.mk.injEq, Prod.swap_prod_mk] at h <;>
            simp [mkC, h, Kind.isWeight]
        · exact .none

/-- One component under `O_merge`. -/
private def mergeC {m : ℕ} (rep : Atom k n → Atom k n) (f : Atom k n → Atom k m)
    (c : Comp (Atom k n)) : Option (Comp (Atom k m)) :=
  if c.kind == .dot && f c.x == f c.y then none
  else if c.kind.isSolid && rep c.x == rep c.y then
    some { c.map f with kind := c.kind.toWeight, y := f c.x }
  else some (c.map f)

/-- `O_merge` for the partition `P` into blocks. -/
private def mergeWith (P : List (List (Atom k n))) (cs : List (Comp (Atom k n))) (d : Coeff) :
    Option (Tracked k n) :=
  let rep := blockRep P
  if cs.any (fun c => c.kind == .xdot && rep c.x == rep c.y) then none else
  let roots := ((List.finRange n).map fun i => rep (Sum.inr i)).dedup
  let f : Atom k n → Atom k roots.length := fun u =>
    match u with
    | .inl a => .inl a
    | .inr i => .inr ⟨roots.idxOf (rep (.inr i)),
        List.idxOf_lt_length_of_mem
          (List.mem_dedup.2 (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))⟩
  some ⟨roots.length, ⟨cs.filterMap (mergeC rep f), d⟩, f⟩

private theorem mergeT_eq_mergeWith (Γ : Graph k n) :
    Γ.mergeT = mergeWith (dotBlocks (allAtoms k n) Γ.comps) Γ.comps Γ.coeff := rfl

private theorem joinBlocks_comm (P : List (List (Atom k n))) (u v : Atom k n) :
    joinBlocks P u v = joinBlocks P v u := by
  unfold joinBlocks
  simp only [Bool.or_comm]

private theorem dotBlocks_rel {cs' cs : List (Comp (Atom k n))} (hR : Forall₂ URel cs' cs) :
    dotBlocks (allAtoms k n) cs' = dotBlocks (allAtoms k n) cs := by
  unfold dotBlocks
  refine List.rel_foldl (fun P Q hPQ c' c h => ?_) rfl hR
  subst hPQ
  obtain ⟨hk, -, -, ⟨hx, hy⟩ | ⟨-, hx, hy⟩⟩ := h
  · rw [hk, hx, hy]
  · rw [hk, hx, hy, joinBlocks_comm]

private theorem mergeC_rel {m : ℕ} (rep : Atom k n → Atom k n) (f : Atom k n → Atom k m)
    {c' c : Comp (Atom k n)} (h : URel c' c) :
    Option.Rel ORel (mergeC rep f c') (mergeC rep f c) := by
  obtain ⟨hk, hm, hl, ⟨hx, hy⟩ | ⟨hw, hx, hy⟩⟩ := h
  · have : c' = c := by
      rcases c' with ⟨_, _, _, _, _⟩
      rcases c with ⟨_, _, _, _, _⟩
      simp_all
    subst this
    cases mergeC rep f c' with
    | none => exact .none
    | some d => exact .some (oRel_refl d)
  · unfold mergeC
    rw [hk, hx, hy, Bool.beq_comm (a := f c.y), Bool.beq_comm (a := rep c.y)]
    split_ifs with h1 h2
    · exact .none
    · refine .some ⟨rfl, by simp [Comp.map, hm], by simp [Comp.map, hl], Or.inl ?_⟩
      simp only [Bool.and_eq_true] at h2
      rcases hc : c.kind with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
        simp_all [Kind.isSolid, Kind.toWeight, Kind.isWeight]
    · exact .some ⟨by simp [Comp.map, hk], by simp [Comp.map, hm], by simp [Comp.map, hl],
        Or.inr (Or.inr ⟨by simp [Comp.map, hx], by simp [Comp.map, hy]⟩)⟩

private theorem mergeWith_rel (P : List (List (Atom k n))) {cs' cs : List (Comp (Atom k n))}
    (d : Coeff) (hR : Forall₂ URel cs' cs) {t' : Tracked k n} (h : mergeWith P cs' d = some t') :
    ∃ t, mergeWith P cs d = some t ∧ TRel t' t := by
  unfold mergeWith at h ⊢
  have hany : (cs'.any fun c => c.kind == .xdot && blockRep P c.x == blockRep P c.y) =
      (cs.any fun c => c.kind == .xdot && blockRep P c.x == blockRep P c.y) := by
    refine forall₂_any (fun c' c h => ?_) hR
    obtain ⟨hk, -, -, ⟨hx, hy⟩ | ⟨-, hx, hy⟩⟩ := h
    · rw [hk, hx, hy]
    · rw [hk, hx, hy, Bool.beq_comm (a := blockRep P c.y)]
  simp only [hany] at h ⊢
  split_ifs at h ⊢
  obtain rfl := Option.some.inj h
  exact ⟨_, rfl, _, _, _, _, rfl, rfl, rfl,
    List.rel_filterMap (fun c' c h => mergeC_rel _ _ h) hR⟩

private theorem mergeT_rel {Γ' Γ : Graph k n} (hc : Γ'.coeff = Γ.coeff)
    (hR : Forall₂ URel Γ'.comps Γ.comps) {t' : Tracked k n} (h : Γ'.mergeT = some t') :
    ∃ t, Γ.mergeT = some t ∧ TRel t' t := by
  rw [mergeT_eq_mergeWith, dotBlocks_rel hR, hc] at h
  rw [mergeT_eq_mergeWith]
  exact mergeWith_rel _ _ hR h

private theorem labels_rel {Γ' Γ : Graph k n} (hR : Forall₂ URel Γ'.comps Γ.comps) :
    Γ'.labels = Γ.labels := by
  unfold Graph.labels
  rw [forall₂_filterMap_eq (fun c' c h => h.2.2.1) hR]

private theorem tRel_self {Γ' Γ : Graph k n} (hc : Γ'.coeff = Γ.coeff)
    (hR : Forall₂ ORel Γ'.comps Γ.comps) : TRel (Tracked.self Γ') (Tracked.self Γ) :=
  ⟨n, Γ', Γ, id, rfl, rfl, hc, hR⟩

/-- Every term of `O_dot` on a graph corresponds to a term of `O_dot` on a graph whose components
are those of the first graph with the ends of some non-weight components exchanged. -/
private theorem oDotT_rel {Γ' Γ : Graph k n} (hc : Γ'.coeff = Γ.coeff)
    (hR : Forall₂ URel Γ'.comps Γ.comps) : ∀ t' ∈ oDotT Γ', ∃ t ∈ oDotT Γ, TRel t' t := by
  intro t' ht
  have hlab := labels_rel hR
  have hany1 : (Γ'.comps.any fun c => (c.kind == .dot || c.kind == .xdot) && c.label.isSome) =
      (Γ.comps.any fun c => (c.kind == .dot || c.kind == .xdot) && c.label.isSome) :=
    forall₂_any (fun c' c h => by rw [h.1, h.2.2.1]) hR
  have hany2 : (Γ'.comps.any fun c =>
      (c.kind == .dot && c.x.isRight && c.y.isRight) || (c.kind.isSolid && c.x == c.y)) =
      (Γ.comps.any fun c =>
      (c.kind == .dot && c.x.isRight && c.y.isRight) || (c.kind.isSolid && c.x == c.y)) := by
    refine forall₂_any (fun c' c h => ?_) hR
    obtain ⟨hk, -, -, ⟨hx, hy⟩ | ⟨-, hx, hy⟩⟩ := h
    · rw [hk, hx, hy]
    · rw [hk, hx, hy, Bool.beq_comm (a := c.y), Bool.and_assoc, Bool.and_comm c.y.isRight,
        ← Bool.and_assoc]
  have hSP := splitPairs_rel hR
  have hemp : Γ'.splitPairs.isEmpty = Γ.splitPairs.isEmpty := forall₂_isEmpty hSP
  have hself : TRel (Tracked.self Γ') (Tracked.self Γ) := tRel_self hc (hR.imp fun _ _ h => h.oRel)
  unfold oDotT at ht ⊢
  simp only [hlab, hany1, hany2, hemp] at ht ⊢
  split_ifs at ht ⊢
  · exact ⟨_, List.mem_singleton_self _, (List.mem_singleton.1 ht) ▸ hself⟩
  · exact ⟨_, List.mem_singleton_self _, (List.mem_singleton.1 ht) ▸ hself⟩
  · obtain ⟨A', hA', hm⟩ := List.mem_filterMap.1 ht
    obtain ⟨A, hA, hAR, hM⟩ := sublist_transfer hSP (splitPairs_nodup Γ') (splitPairs_nodup Γ)
      (List.mem_sublists.1 hA')
    obtain ⟨hc', hR'⟩ := dotChoice_rel hc hR hM hAR
    obtain ⟨t, ht, hT⟩ := mergeT_rel hc' hR' hm
    exact ⟨t, List.mem_filterMap.2 ⟨A, List.mem_sublists.2 hA, ht⟩, hT⟩

/-- Every term of `O_dot` applied after the reversal of every solid edge corresponds to a term of
`O_dot` applied before it. -/
private theorem bind_swapSolid_rel (E : TExpansion k n) :
    ∀ t' ∈ E.swapSolid.bind (fun _ g => oDotT g),
      ∃ t ∈ E.bind (fun _ g => oDotT g), TRel t' t := by
  intro t' ht'
  simp only [TExpansion.bind, TExpansion.swapSolid, List.flatMap_map, List.mem_flatMap,
    List.mem_map] at ht'
  obtain ⟨e, he, s', hs', rfl⟩ := ht'
  obtain ⟨s, hs, m, g', g, f, rfl, rfl, hc, hR⟩ :=
    oDotT_rel (Γ' := e.g.swapSolid) (Γ := e.g) rfl (forall₂_swapSolid e.g.comps) s' hs'
  refine ⟨⟨m, g, f ∘ e.f⟩, ?_, m, g', g, f ∘ e.f, rfl, rfl, hc, hR⟩
  simp only [TExpansion.bind, List.mem_flatMap, List.mem_map]
  exact ⟨e, he, ⟨m, g, f⟩, hs, rfl⟩

/-- Every term of the transposed `GG` expansion at `x` corresponds to a term of the `GG`
expansion at `x` of the graph with every solid edge reversed. -/
theorem oGGTT_rel (x : Atom k n) (Γ : Graph k n) :
    ∀ t' ∈ oGGTT x Γ, ∃ t ∈ oGGT x Γ.swapSolid, TRel t' t := by
  intro t' ht'
  have hpl : Γ.swapSolid.comps.all Comp.isPlainB = Γ.comps.all Comp.isPlainB := by
    simp [Graph.swapSolid, List.all_map, Function.comp_def, isPlainB_swapSolid]
  have hself : TRel (Tracked.self Γ) (Tracked.self Γ.swapSolid) := by
    refine tRel_self rfl ?_
    simp only [Graph.swapSolid]
    rw [forall₂_map_right_iff, forall₂_same]
    exact fun c _ => oRel_swapSolid_right c
  unfold oGGTT at ht'
  unfold oGGT
  rw [hpl]
  by_cases hp : (!(Γ.comps.all Comp.isPlainB)) = true
  · simp only [hp, ite_true] at ht' ⊢
    exact ⟨_, List.mem_singleton_self _, (List.mem_singleton.1 ht') ▸ hself⟩
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at ht' ⊢
    cases h1 : ggPos x Γ.swapSolid with
    | some E =>
      simp only [h1] at ht' ⊢
      exact bind_swapSolid_rel E t' ht'
    | none =>
      simp only [h1] at ht' ⊢
      cases h2 : ggPos x Γ.swapSolid.conj with
      | some E =>
        simp only [h2] at ht' ⊢
        exact bind_swapSolid_rel E.conj t' ht'
      | none =>
        simp only [h2] at ht' ⊢
        exact ⟨_, List.mem_singleton_self _, (List.mem_singleton.1 ht') ▸ hself⟩

end Corr

section CorrTransfer

open List

variable {k n : ℕ}

private theorem exists_sym_rel {V : Type*} {R : Comp V → Comp V → Prop} {l' l : List (Comp V)}
    (hR : Forall₂ R l' l) (P : Comp V → Prop) (hP : ∀ c' c, R c' c → (P c' ↔ P c))
    (hends : ∀ c' c, R c' c → P c → (c'.x = c.x ∧ c'.y = c.y) ∨ (c'.x = c.y ∧ c'.y = c.x))
    (u v : V) :
    (∃ c ∈ l', P c ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u)) ↔
      ∃ c ∈ l, P c ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u) := by
  constructor
  · rintro ⟨c', hc', hp, he⟩
    obtain ⟨c, hc, hr⟩ := forall₂_mem_left hR c' hc'
    have hp' := (hP c' c hr).1 hp
    refine ⟨c, hc, hp', ?_⟩
    rcases hends c' c hr hp' with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy] at he <;> tauto
  · rintro ⟨c, hc, hp, he⟩
    obtain ⟨c', hc', hr⟩ := forall₂_mem_right hR c hc
    refine ⟨c', hc', (hP c' c hr).2 hp, ?_⟩
    rcases hends c' c hr hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy] <;> tauto

private theorem fromRel_rel {V : Type*} {R : Comp V → Comp V → Prop} {l' l : List (Comp V)}
    (hR : Forall₂ R l' l) (P : Comp V → Prop) (hP : ∀ c' c, R c' c → (P c' ↔ P c))
    (hends : ∀ c' c, R c' c → P c → (c'.x = c.x ∧ c'.y = c.y) ∨ (c'.x = c.y ∧ c'.y = c.x)) :
    SimpleGraph.fromRel (fun u v => ∃ c ∈ l', P c ∧ c.x = u ∧ c.y = v) =
      SimpleGraph.fromRel (fun u v => ∃ c ∈ l, P c ∧ c.x = u ∧ c.y = v) := by
  ext u v
  simp only [SimpleGraph.fromRel_adj]
  have key : ∀ l : List (Comp V), ((∃ c ∈ l, P c ∧ c.x = u ∧ c.y = v) ∨
      ∃ c ∈ l, P c ∧ c.x = v ∧ c.y = u) ↔
      ∃ c ∈ l, P c ∧ (c.x = u ∧ c.y = v ∨ c.x = v ∧ c.y = u) := by
    intro l
    constructor
    · rintro (⟨c, hc, hp, h⟩ | ⟨c, hc, hp, h⟩)
      exacts [⟨c, hc, hp, Or.inl h⟩, ⟨c, hc, hp, Or.inr h⟩]
    · rintro ⟨c, hc, hp, h | h⟩
      exacts [Or.inl ⟨c, hc, hp, h⟩, Or.inr ⟨c, hc, hp, h⟩]
  rw [key, key, exists_sym_rel hR P hP hends]


end CorrTransfer

section GGTNormal

open List

variable {k n : ℕ}

private theorem oRel_ends_of_not_weight' {V : Type*} {c' c : Comp V} (h : ORel c' c)
    (hw : c.kind.isWeight = false) : (c'.x = c.x ∧ c'.y = c.y) ∨ (c'.x = c.y ∧ c'.y = c.x) := by
  obtain ⟨-, -, -, h | h | h⟩ := h
  · rw [hw] at h
    exact absurd h (by simp)
  · exact Or.inl h
  · exact Or.inr h

private theorem edgeGraph_eq_nw {m : ℕ} {g : Graph k m} (hP : g.Plain) :
    g.edgeGraph = SimpleGraph.fromRel
      (fun u v => ∃ c ∈ g.comps, c.kind.isWeight = false ∧ c.x = u ∧ c.y = v) := by
  ext u v
  simp only [Graph.edgeGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨huv, ⟨c, hc, h1, h2⟩ | ⟨c, hc, h1, h2⟩⟩
    · refine ⟨huv, Or.inl ⟨c, hc, ?_, h1, h2⟩⟩
      by_contra hw
      simp only [Bool.not_eq_false] at hw
      exact huv (h1 ▸ h2 ▸ ((hP c hc).2.2.2.2.1 hw).symm)
    · refine ⟨huv, Or.inr ⟨c, hc, ?_, h1, h2⟩⟩
      by_contra hw
      simp only [Bool.not_eq_false] at hw
      exact huv (h1 ▸ h2 ▸ ((hP c hc).2.2.2.2.1 hw))
  · rintro ⟨huv, ⟨c, hc, -, h1, h2⟩ | ⟨c, hc, -, h1, h2⟩⟩
    · exact ⟨huv, Or.inl ⟨c, hc, h1, h2⟩⟩
    · exact ⟨huv, Or.inr ⟨c, hc, h1, h2⟩⟩

/-- Normal regular graphs with corresponding components. -/
private theorem normal_rel {m C : ℕ} {g' g : Graph k m} (hR : Forall₂ ORel g'.comps g.comps)
    (hP' : g'.Plain) (hP : g.Plain) (hN : g.Normal C) : g'.Normal C := by
  obtain ⟨⟨hsz, hcon, hint, hnoint⟩, hsol, hxs⟩ := hN
  have hE : g'.edgeGraph = g.edgeGraph := by
    rw [edgeGraph_eq_nw hP', edgeGraph_eq_nw hP]
    exact fromRel_rel hR (fun c => c.kind.isWeight = false) (fun c' c h => by rw [h.1])
      fun c' c h hp => oRel_ends_of_not_weight' h hp
  have hW : g'.wavedThetaGraph = g.wavedThetaGraph :=
    fromRel_rel hR (fun c => c.kind.joinsMol = true ∧ c.kind ≠ .dot ∨ c.kind.isDiffusive = true)
      (fun c' c h => by rw [h.1])
      fun c' c h hp => oRel_ends_of_not_weight' h (Kind.isWeight_of_molT _ hp)
  refine ⟨⟨by rw [hR.length_eq]; exact hsz, by rw [hE]; exact hcon,
    fun a b => by rw [hW]; exact hint a b, ?_⟩, ?_, ?_⟩
  · intro c' hc' hk
    obtain ⟨c, hc, hr⟩ := forall₂_mem_left hR c' hc'
    have hk' : c.kind = .dot := by rw [← hr.1]; exact hk
    rcases oRel_ends_of_not_weight' hr (by rw [hk']; rfl) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2] <;> rcases hnoint c hc hk' with h | h <;> simp [h]
  · intro c' hc' hk
    obtain ⟨c, hc, hr⟩ := forall₂_mem_left hR c' hc'
    have hk' : c.kind.isSolid = true := by rw [← hr.1]; exact hk
    rcases oRel_ends_of_not_weight' hr (Kind.isWeight_of_solid _ hk') with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2]
    · exact hsol c hc hk'
    · exact fun h => hsol c hc hk' h.symm
  · intro u v huv
    rw [exists_sym_rel hR (fun c => c.kind = .xdot) (fun c' c h => by rw [h.1])
        (fun c' c h hp => oRel_ends_of_not_weight' h (by rw [hp]; rfl)) u v,
      exists_sym_rel hR (fun c => c.kind.isSolid = true) (fun c' c h => by rw [h.1])
        (fun c' c h hp => oRel_ends_of_not_weight' h (Kind.isWeight_of_solid _ hp)) u v]
    exact hxs u v huv

/-- The outputs of the transposed `GG` expansion that are plain are normal regular with bound
`2 C + 16`. -/
private theorem oGGTT_normal {C : ℕ} {x : Atom k n} {Γ : Graph k n} (hN : Γ.Normal C) (hP : Γ.Plain)
    (hx : x.isRight = true) {t : Tracked k n} (ht : t ∈ oGGTT x Γ) (hPt : t.g.Plain) :
    t.g.Normal (2 * C + 16) := by
  obtain ⟨t₀, ht₀, m, g', g, f, rfl, rfl, -, hR⟩ := oGGTT_rel x Γ t ht
  have hc := oGG_canonical k n C x Γ.swapSolid hx (Graph.swapSolid_Normal hN)
    ((swapSolid_basic k n Γ).2.2.2.1.2 hP) _ ht₀
  exact normal_rel hR hPt hc.2.1 hc.1

end GGTNormal

section WLen

variable {k n : ℕ}

end WLen

section Select

variable {k n : ℕ}

end Select

section QBounds

variable {k n : ℕ}

end QBounds

section BChoice

end BChoice

section Values

variable {k n : ℕ}

end Values

section Recursion

variable {k : ℕ}

end Recursion



section Instances

/-! ### Decidability on atomic graphs -/

instance instDecLabelFreeS {k n : ℕ} (Γ : Graph k n) : Decidable Γ.LabelFree :=
  inferInstanceAs (Decidable (∀ c ∈ Γ.comps, c.label = none))

/-- The kind is not a `(G_{xx})⁻¹` weight. -/
def Kind.notInvB : Kind → Bool
  | .inv _ => false
  | _ => true

/-- The kind is not a `W_D` weight. -/
def Kind.notWDB : Kind → Bool
  | .wD _ _ => false
  | _ => true

private theorem notInvB_iff (κ : Kind) : (∀ ch, κ ≠ .inv ch) ↔ κ.notInvB = true := by
  cases κ <;> simp [Kind.notInvB]

private theorem notWDB_iff (κ : Kind) : (∀ ch d, κ ≠ .wD ch d) ↔ κ.notWDB = true := by
  cases κ <;> simp [Kind.notWDB]

instance instDecPlain {k n : ℕ} (Γ : Graph k n) : Decidable Γ.Plain :=
  decidable_of_iff (∀ c ∈ Γ.comps, c.minor = [] ∧ c.kind.notInvB = true ∧ c.kind.notWDB = true ∧
    (c.kind = .dot → c.x ≠ c.y) ∧
    ((c.kind.isWeight = true → c.y = c.x) ∧ (c.label.isSome = true → c.kind.isRandom = true)))
    (by simp only [Graph.Plain, Comp.WF, notInvB_iff, notWDB_iff])

end Instances

section InstancesMain

end InstancesMain

end RBM8D.Graphs
