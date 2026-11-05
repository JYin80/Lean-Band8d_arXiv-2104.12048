import RBM8D.Graph.Local.Transposed
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import RBM8D.Graph.Deterministic
import RBM8D.Graph.Standard
import RBM8D.Graph.Local.Basic
import RBM8D.Graph.MolMerge
import RBM8D.Graph.MolSplit
import RBM8D.Graph.MolDot

/-!
# Local expansions of sequentially pre-deterministic and globally standard graphs

The local expansions of Step 1 of [II, Strategy 6.6], with the `GG` expansion in the form whose
waved edge in the main term joins `x` to an internal atom, and [II, Lemma 5.10] and
[II, Lemma 6.4 (1), (2)] for them, in the block reading of the dotted edges at `⊗`, `⊕`, `⊖`
(`RBM8D.Graph.MolRead`) and the reading `Graph.QLabelInMISB` of [II, Def 6.3 (3)].
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-- The local expansions of [II, Defs 4.3–4.6] at the atom `x`: `O_weight` (`0`), `O_multi-e`
(`1`), `O_GG` (`2`), `O_GḠ` (`3`), and the transposed `O_GG` (`4`). -/
def localOp' {k n : ℕ} (o : Fin 5) (x : Atom k n) (Γ : Graph k n) : TExpansion k n :=
  match o with
  | 0 => oWeightT x Γ
  | 1 => oMultiET x Γ
  | 2 => oGGT x Γ
  | 3 => oGGbarT x Γ
  | 4 => oGGTT x Γ

/-- The conditions of the two forms of the `GG` expansion at `x` in [II, Strategy 6.6, Step 1]:
`O_GG` (`2`) at an internal atom whose outgoing solid edges end at internal atoms, the transposed
`O_GG` (`4`) at an internal atom whose incoming solid edges start at internal atoms. -/
def Graph.LocSide {k n : ℕ} (o : Fin 5) (x : Atom k n) (Γ : Graph k n) : Prop :=
  (o = 2 → x.isRight = true → Γ.GGOutInt x) ∧ (o = 4 → x.isRight = true → Γ.GGInInt x)

/-! ## Isolated subsets carried back along a map of the vertices -/

section Pull

variable {V E V' E' V'' E'' : Type}

/-- Every proper isolated subset of `G'` is read back along `φ` as a proper isolated subset of `G`
with the same internal vertices (through `φ`), and is weakly isolated when that subset is. -/
private def Local_Pull (G : MGraph V E) (G' : MGraph V' E') (φ : V → V') : Prop :=
  (∀ v ∈ G.int, φ v ∈ G'.int) ∧
  ∀ P', G'.IsProperIso G'.int P' → ∃ P, G.IsProperIso G.int P ∧
    (∀ v ∈ G.int, (v ∈ P ↔ φ v ∈ P')) ∧ (G.IsWeaklyIso P → G'.IsWeaklyIso P')

private theorem Local_pull_id (G : MGraph V E) : Local_Pull G G id :=
  ⟨fun _ h => h, fun P' h => ⟨P', h, fun _ _ => Iff.rfl, id⟩⟩

private theorem Local_pull_trans {G : MGraph V E} {G' : MGraph V' E'} {G'' : MGraph V'' E''}
    {φ : V → V'} {ψ : V' → V''} (h₁ : Local_Pull G G' φ) (h₂ : Local_Pull G' G'' ψ) :
    Local_Pull G G'' (ψ ∘ φ) := by
  refine ⟨fun v hv => h₂.1 _ (h₁.1 v hv), fun P'' hP'' => ?_⟩
  obtain ⟨P', hP', hm', hw'⟩ := h₂.2 P'' hP''
  obtain ⟨P, hP, hm, hw⟩ := h₁.2 P' hP'
  exact ⟨P, hP, fun v hv => (hm v hv).trans (hm' _ (h₁.1 v hv)), fun h => hw' (hw h)⟩

/-- The minimal isolated subset is carried along `φ`. -/
private theorem Local_pull_MIS {G : MGraph V E} {G' : MGraph V' E'} {φ : V → V'}
    (h : Local_Pull G G' φ) {v : V} (hv : v ∈ G.MIS) : φ v ∈ G'.MIS := by
  classical
  simp only [MGraph.MIS, Finset.mem_filter] at hv ⊢
  refine ⟨h.1 v hv.1, fun P' hP' => ?_⟩
  obtain ⟨P, hP, hm, -⟩ := h.2 P' hP'
  exact (hm v hv.1).1 (hv.2 P hP)

/-- Globally standard graphs are carried along `φ` to sequentially pre-deterministic graphs. -/
private theorem Local_pull_gs [DecidableEq V] [DecidableEq E] [DecidableEq V'] [DecidableEq E']
    {G : MGraph V E} {G' : MGraph V' E'} {φ : V → V'} (h : Local_Pull G G' φ)
    (hg : G.GloballyStandard) (hs : G'.SPD) : G'.GloballyStandard := by
  refine ⟨hs, fun P' hP' => ?_⟩
  obtain ⟨P, hP, -, hw⟩ := h.2 P' hP'
  exact hw (hg.2 P hP)

/-- A doubly connected graph has two distinct internal edges crossing every nonempty proper subset
of its internal vertices. -/
private theorem Local_dc_two {G : MGraph V E} (hdc : G.DC) {P : Finset V} (hP : P ⊆ G.int)
    (hne : P.Nonempty) (hnt : ¬ G.int ⊆ P) :
    ∃ e₁ e₂, e₁ ≠ e₂ ∧ G.Crosses P e₁ ∧ G.Crosses P e₂ ∧ (G.ends e₁).1 ∈ G.int ∧
      (G.ends e₁).2 ∈ G.int ∧ (G.ends e₂).1 ∈ G.int ∧ (G.ends e₂).2 ∈ G.int := by
  obtain ⟨bk, bu, hd, hbk, hbu, hsk, hsu⟩ := hdc
  obtain ⟨e₁, he₁, hc₁, h11, h12, hcut₁⟩ := hsk P hP hne hnt
  obtain ⟨e₂, he₂, hc₂, h21, h22, hcut₂⟩ := hsu P hP hne hnt
  refine ⟨e₁, e₂, fun h => Finset.disjoint_left.1 hd he₁ (h ▸ he₂),
    ⟨hc₁, by rw [hbk e₁ he₁]; simp, Or.inl h11, Or.inl h12, hcut₁⟩,
    ⟨hc₂, ?_, Or.inl h21, Or.inl h22, hcut₂⟩, h11, h12, h21, h22⟩
  rcases hbu e₂ he₂ with h | h | h <;> rw [h] <;> simp

/-- Three distinct crossing edges: not isolated. -/
private theorem Local_not_iso_three {G : MGraph V E} {P : Finset V} {e₁ e₂ e₃ : E}
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) (c₁ : G.Crosses P e₁) (c₂ : G.Crosses P e₂)
    (c₃ : G.Crosses P e₃) : ¬ G.IsIsolated P := by
  rintro ⟨-, f₁, f₂, -, hf⟩
  rcases (hf e₁).1 c₁ with rfl | rfl <;> rcases (hf e₂).1 c₂ with rfl | rfl <;>
    rcases (hf e₃).1 c₃ with rfl | rfl <;> simp_all

/-- In a doubly connected graph, a proper nonempty subset of the internal vertices that contains
the internal end of a present edge, not red, to a vertex outside the internal vertices is not
isolated. -/
private theorem Local_not_iso_ext {G : MGraph V E} (hdc : G.DC) {P : Finset V} (hP : P ⊆ G.int)
    (hne : P.Nonempty) (hnt : ¬ G.int ⊆ P) {e : E} (hc : G.cls e ≠ none)
    (hr : G.cls e ≠ some .minus) (h1 : (G.ends e).1 ∈ P) (h2 : G.IsVtx (G.ends e).2)
    (h2' : (G.ends e).2 ∉ G.int) : ¬ G.IsIsolated P := by
  obtain ⟨e₁, e₂, h12, c₁, c₂, -, i₁, -, i₂⟩ := Local_dc_two hdc hP hne hnt
  have ce : G.Crosses P e :=
    ⟨hc, hr, Or.inl (hP h1), h2, Or.inl ⟨h1, fun h => h2' (hP h)⟩⟩
  have hne₁ : e ≠ e₁ := by
    rintro rfl
    exact h2' i₁
  have hne₂ : e ≠ e₂ := by
    rintro rfl
    exact h2' i₂
  exact Local_not_iso_three hne₁ hne₂ h12 ce c₁ c₂

/-- Three values in a set of two, the last two distinct: the first is one of them. -/
private theorem Local_two_vals {α : Type} {a b c f₁ f₂ : α} (ha : a = f₁ ∨ a = f₂)
    (hb : b = f₁ ∨ b = f₂) (hc : c = f₁ ∨ c = f₂) (hbc : b ≠ c) (hab : a ≠ b) (hac : a ≠ c) :
    False := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    first | exact hbc rfl | exact hab rfl | exact hac rfl

/-- The criterion for `Local_Pull`: `φ` maps the internal vertices of `G` onto those of `G'`, `G` is
doubly connected, and for every set `P'` of internal vertices of `G'`, either `P'` is not isolated,
or the crossing edges and the red crossing edges of its preimage are sent injectively to crossing
edges and red crossing edges of `P'`. -/
private theorem Local_pull_of [DecidableEq V'] {G : MGraph V E} {G' : MGraph V' E'} (φ : V → V')
    (hi : ∀ v ∈ G.int, φ v ∈ G'.int) (hs : ∀ w ∈ G'.int, ∃ v ∈ G.int, φ v = w) (hdc : G.DC)
    (hcr : ∀ P', G'.IsProperIso G'.int P' →
      ∃ g : E → E',
        (∀ e, G.Crosses (G.int.filter fun v => φ v ∈ P') e → G'.Crosses P' (g e)) ∧
        (∀ e₁ e₂, G.Crosses (G.int.filter fun v => φ v ∈ P') e₁ →
          G.Crosses (G.int.filter fun v => φ v ∈ P') e₂ → g e₁ = g e₂ → e₁ = e₂) ∧
        (∀ e, G.RedCrosses (G.int.filter fun v => φ v ∈ P') e → G'.RedCrosses P' (g e)) ∧
        (∀ e₁ e₂, G.RedCrosses (G.int.filter fun v => φ v ∈ P') e₁ →
          G.RedCrosses (G.int.filter fun v => φ v ∈ P') e₂ → g e₁ = g e₂ → e₁ = e₂)) :
    Local_Pull G G' φ := by
  classical
  refine ⟨hi, fun P' hP' => ?_⟩
  obtain ⟨hiso, hlt⟩ := hP'
  set P := G.int.filter fun v => φ v ∈ P' with hPdef
  obtain ⟨hsub, f₁, f₂, hf12, hf⟩ := hiso
  have hPsub : P ⊆ G.int := Finset.filter_subset _ _
  have hPne : P.Nonempty := by
    have hc := (hf f₁).2 (Or.inl rfl)
    obtain ⟨-, -, -, -, hcut⟩ := hc
    have : ∃ w ∈ P', True := by
      rcases hcut with ⟨h, -⟩ | ⟨-, h⟩
      · exact ⟨_, h, trivial⟩
      · exact ⟨_, h, trivial⟩
    obtain ⟨w, hw, -⟩ := this
    obtain ⟨v, hv, rfl⟩ := hs w (hsub hw)
    exact ⟨v, Finset.mem_filter.2 ⟨hv, hw⟩⟩
  have hPnt : ¬ G.int ⊆ P := by
    obtain ⟨w, hw, hwP⟩ := Finset.exists_of_ssubset hlt
    obtain ⟨v, hv, rfl⟩ := hs w hw
    intro h
    exact hwP (Finset.mem_filter.1 (h hv)).2
  obtain ⟨g, hg1, hg2, hg3, hg4⟩ := hcr P' ⟨⟨hsub, f₁, f₂, hf12, hf⟩, hlt⟩
  obtain ⟨e₁, e₂, h12, c₁, c₂, -⟩ := Local_dc_two hdc hPsub hPne hPnt
  have hiso : G.IsIsolated P := by
    refine ⟨hPsub, e₁, e₂, h12, fun e => ⟨fun he => ?_, ?_⟩⟩
    · have hge := (hf (g e)).1 (hg1 e he)
      have hg₁ := (hf (g e₁)).1 (hg1 e₁ c₁)
      have hg₂ := (hf (g e₂)).1 (hg1 e₂ c₂)
      have hne : g e₁ ≠ g e₂ := fun h => h12 (hg2 _ _ c₁ c₂ h)
      by_cases h1 : g e = g e₁
      · exact Or.inl (hg2 _ _ he c₁ h1)
      · by_cases h2 : g e = g e₂
        · exact Or.inr (hg2 _ _ he c₂ h2)
        · exfalso
          exact Local_two_vals hge hg₁ hg₂ hne h1 h2
    · rintro (rfl | rfl)
      · exact c₁
      · exact c₂
  refine ⟨P, ⟨hiso, Finset.ssubset_iff_subset_ne.2 ⟨hPsub, fun h => hPnt (h ▸ le_rfl)⟩⟩,
    fun v hv => ?_, fun ⟨_, r₁, r₂, hr12, hr₁, hr₂⟩ => ?_⟩
  · simp [hPdef, hv]
  · exact ⟨⟨hsub, f₁, f₂, hf12, hf⟩, g r₁, g r₂, fun h => hr12 (hg4 _ _ hr₁ hr₂ h), hg3 _ hr₁,
      hg3 _ hr₂⟩

end Pull

/-! ## Lists of edges -/

section Lists

/-- A permutation of lists is a bijection of their positions. -/
private theorem Local_perm_fin {α : Type*} {L L' : List α} (h : L.Perm L') :
    ∃ g : Fin L.length → Fin L'.length, Function.Bijective g ∧ ∀ i, L'[g i] = L[i] := by
  induction h with
  | nil => exact ⟨id, Function.bijective_id, fun i => rfl⟩
  | @cons x l l' _ ih =>
    obtain ⟨g, hg, hv⟩ := ih
    refine ⟨Fin.cases ⟨0, by simp⟩ (fun i => (g i).succ), ⟨fun i j hij => ?_, fun j => ?_⟩,
      fun i => ?_⟩
    · induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => rfl
        | succ j => exact absurd hij.symm (Fin.succ_ne_zero _)
      | succ i =>
        induction j using Fin.cases with
        | zero => exact absurd hij (Fin.succ_ne_zero _)
        | succ j =>
          simp only [Fin.cases_succ, Fin.succ_inj] at hij
          rw [hg.1 hij]
    · induction j using Fin.cases with
      | zero => exact ⟨0, rfl⟩
      | succ j =>
        obtain ⟨i, rfl⟩ := hg.2 j
        exact ⟨i.succ, by simp⟩
    · induction i using Fin.cases with
      | zero => rfl
      | succ i => simpa using hv i
  | @swap x y l =>
    let σ : ℕ → ℕ := fun m => if m = 0 then 1 else if m = 1 then 0 else m
    have hσ : ∀ m, σ (σ m) = m := by
      intro m
      by_cases h0 : m = 0
      · simp [σ, h0]
      · by_cases h1 : m = 1
        · simp [σ, h1]
        · simp [σ, h0, h1]
    have hσl : ∀ m, m < l.length + 2 → σ m < l.length + 2 := by
      intro m hm
      simp only [σ]
      split_ifs <;> omega
    refine ⟨fun i => ⟨σ i, by have := hσl i (by simpa using i.2); simp only [List.length_cons]; omega⟩,
      ⟨fun i j hij => Fin.ext ?_, fun j => ⟨⟨σ j, by
        have := hσl j (by simpa using j.2); simp only [List.length_cons]; omega⟩,
        Fin.ext (hσ j)⟩⟩, fun i => ?_⟩
    · have := congrArg (fun k : Fin _ => σ k) hij
      simpa [hσ] using this
    · obtain ⟨i, hi⟩ := i
      match i, hi with
      | 0, _ => rfl
      | 1, _ => rfl
      | i + 2, _ => simp [σ]
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨g₁, hg₁, hv₁⟩ := ih₁
    obtain ⟨g₂, hg₂, hv₂⟩ := ih₂
    exact ⟨g₂ ∘ g₁, hg₂.comp hg₁, fun i => by simp [hv₂, hv₁]⟩

end Lists


/-! ## Carried molecular multigraphs -/

section Carry

variable {V E V' E' V'' E'' : Type}

/-- No edge of class ghost. -/
private def Local_NG (G : MGraph V E) : Prop := ∀ e, G.cls e ≠ some .ghost

/-- `G'` is carried from `G` along `φ`: on graphs without ghost edges whose internal and external
vertices are distinct, the sequentially pre-deterministic property passes from `G` to `G'`, these
two properties are kept, and the isolated subsets of `G'` are read back along `φ`. -/
private def Local_Carry [DecidableEq V] [DecidableEq E] [DecidableEq V'] [DecidableEq E']
    (G : MGraph V E) (G' : MGraph V' E') (φ : V → V') : Prop :=
  Disjoint G.int G.ext → Local_NG G → G.SPD →
    G'.SPD ∧ Local_NG G' ∧ Disjoint G'.int G'.ext ∧ Local_Pull G G' φ

private theorem Local_carry_refl [DecidableEq V] [DecidableEq E] (G : MGraph V E) :
    Local_Carry G G id := fun hd hg hs => ⟨hs, hg, hd, Local_pull_id G⟩

private theorem Local_carry_trans_id [DecidableEq V] [DecidableEq E] [DecidableEq E']
    [DecidableEq E''] {G : MGraph V E} {G' : MGraph V E'} {G'' : MGraph V E''}
    (h₁ : Local_Carry G G' id) (h₂ : Local_Carry G' G'' id) : Local_Carry G G'' id := by
  intro hd hg hs
  obtain ⟨s₁, g₁, d₁, p₁⟩ := h₁ hd hg hs
  obtain ⟨s₂, g₂, d₂, p₂⟩ := h₂ d₁ g₁ s₁
  exact ⟨s₂, g₂, d₂, Local_pull_trans p₁ p₂⟩

private theorem Local_carry_trans [DecidableEq V] [DecidableEq E] [DecidableEq V'] [DecidableEq E']
    [DecidableEq V''] [DecidableEq E''] {G : MGraph V E} {G' : MGraph V' E'}
    {G'' : MGraph V'' E''} {φ : V → V'} {ψ : V' → V''} (h₁ : Local_Carry G G' φ)
    (h₂ : Local_Carry G' G'' ψ) : Local_Carry G G'' (ψ ∘ φ) := by
  intro hd hg hs
  obtain ⟨s₁, g₁, d₁, p₁⟩ := h₁ hd hg hs
  obtain ⟨s₂, g₂, d₂, p₂⟩ := h₂ d₁ g₁ s₁
  exact ⟨s₂, g₂, d₂, Local_pull_trans p₁ p₂⟩

/-- A cut of the preimage of `P'` along `φ` is a cut of `P'`, when `φ` maps the internal and the
external vertices of `G` to those of `G'` and `P'` consists of internal vertices of `G'`, whose
internal and external vertices are distinct. -/
private theorem Local_cut_map [DecidableEq V'] {G : MGraph V E} {G' : MGraph V' E'} {φ : V → V'}
    (hi : ∀ v ∈ G.int, φ v ∈ G'.int) (hx : ∀ v ∈ G.ext, φ v ∈ G'.ext)
    (hd : Disjoint G'.int G'.ext) {P' : Finset V'} (hP' : P' ⊆ G'.int) {a b : V}
    (ha : G.IsVtx a) (hb : G.IsVtx b) (h : a ∈ G.int.filter (fun v => φ v ∈ P') ∧
      b ∉ G.int.filter (fun v => φ v ∈ P')) : φ a ∈ P' ∧ φ b ∉ P' := by
  refine ⟨(Finset.mem_filter.1 h.1).2, fun hb' => ?_⟩
  rcases hb with hb | hb
  · exact h.2 (Finset.mem_filter.2 ⟨hb, hb'⟩)
  · exact Finset.disjoint_left.1 hd (hP' hb') (hx b hb)

/-- `Local_Pull` from a map of the edges: every present edge of `G` that is not a loop is sent to
a present edge of `G'` with the images of its ends (in either order), red exactly when it is red,
injectively. -/
private theorem Local_pull_edgewise [DecidableEq V'] {G : MGraph V E} {G' : MGraph V' E'}
    (φ : V → V') (g : E → E') (hi : ∀ v ∈ G.int, φ v ∈ G'.int)
    (hs : ∀ w ∈ G'.int, ∃ v ∈ G.int, φ v = w) (hx : ∀ v ∈ G.ext, φ v ∈ G'.ext) (hdc : G.DC)
    (hd : Disjoint G'.int G'.ext)
    (hc : ∀ e, G.cls e ≠ none → (G.ends e).1 ≠ (G.ends e).2 →
      G'.cls (g e) ≠ none ∧ (G'.cls (g e) = some .minus ↔ G.cls e = some .minus) ∧
      (G'.ends (g e) = (φ (G.ends e).1, φ (G.ends e).2) ∨
        G'.ends (g e) = (φ (G.ends e).2, φ (G.ends e).1)))
    (hinj : ∀ e₁ e₂, G.cls e₁ ≠ none → G.cls e₂ ≠ none → (G.ends e₁).1 ≠ (G.ends e₁).2 →
      (G.ends e₂).1 ≠ (G.ends e₂).2 → g e₁ = g e₂ → e₁ = e₂) :
    Local_Pull G G' φ := by
  have hv : ∀ v, G.IsVtx v → G'.IsVtx (φ v) := by
    rintro v (h | h)
    · exact Or.inl (hi v h)
    · exact Or.inr (hx v h)
  have key : ∀ (P' : Finset V'), P' ⊆ G'.int → ∀ e,
      G.cls e ≠ none → G.IsVtx (G.ends e).1 → G.IsVtx (G.ends e).2 →
      G.Cut (G.int.filter fun v => φ v ∈ P') e →
      (G.ends e).1 ≠ (G.ends e).2 ∧ G'.IsVtx (G'.ends (g e)).1 ∧ G'.IsVtx (G'.ends (g e)).2 ∧
        G'.Cut P' (g e) := by
    intro P' hP' e hce h1 h2 hcut
    have hne : (G.ends e).1 ≠ (G.ends e).2 := by
      intro h
      rcases hcut with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [h] at a <;> contradiction
    refine ⟨hne, ?_⟩
    obtain ⟨-, -, he⟩ := hc e hce hne
    unfold MGraph.Cut
    rcases hcut with hcut | hcut
    · have := Local_cut_map hi hx hd hP' h1 h2 hcut
      rcases he with he | he <;> rw [he]
      · exact ⟨hv _ h1, hv _ h2, Or.inl this⟩
      · exact ⟨hv _ h2, hv _ h1, Or.inr ⟨this.2, this.1⟩⟩
    · have := Local_cut_map hi hx hd hP' h2 h1 ⟨hcut.2, hcut.1⟩
      rcases he with he | he <;> rw [he]
      · exact ⟨hv _ h1, hv _ h2, Or.inr ⟨this.2, this.1⟩⟩
      · exact ⟨hv _ h2, hv _ h1, Or.inl this⟩
  refine Local_pull_of φ hi hs hdc fun P' hP'' => ?_
  have hP' : P' ⊆ G'.int := hP''.1.1
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · rintro e ⟨hce, hr, h1, h2, hcut⟩
    obtain ⟨hne, v1, v2, hcut'⟩ := key P' hP' e hce h1 h2 hcut
    obtain ⟨hc', hr', -⟩ := hc e hce hne
    exact ⟨hc', fun h => hr (hr'.1 h), v1, v2, hcut'⟩
  · rintro e₁ e₂ ⟨c₁, -, a₁, b₁, k₁⟩ ⟨c₂, -, a₂, b₂, k₂⟩ h
    exact hinj e₁ e₂ c₁ c₂ (key P' hP' e₁ c₁ a₁ b₁ k₁).1 (key P' hP' e₂ c₂ a₂ b₂ k₂).1 h
  · rintro e ⟨hr, h1, h2, hcut⟩
    have hce : G.cls e ≠ none := by rw [hr]; simp
    obtain ⟨hne, v1, v2, hcut'⟩ := key P' hP' e hce h1 h2 hcut
    obtain ⟨-, hr', -⟩ := hc e hce hne
    exact ⟨hr'.2 hr, v1, v2, hcut'⟩
  · rintro e₁ e₂ ⟨r₁, a₁, b₁, k₁⟩ ⟨r₂, a₂, b₂, k₂⟩ h
    have c₁ : G.cls e₁ ≠ none := by rw [r₁]; simp
    have c₂ : G.cls e₂ ≠ none := by rw [r₂]; simp
    exact hinj e₁ e₂ c₁ c₂ (key P' hP' e₁ c₁ a₁ b₁ k₁).1 (key P' hP' e₂ c₂ a₂ b₂ k₂).1 h

/-- A change of names carries the graph along the map of the vertices. -/
private theorem Local_carry_tr [DecidableEq V] [DecidableEq E] [DecidableEq V'] [DecidableEq E']
    {G : MGraph V E} {G' : MGraph V' E'} {f : V → V'} {g : E → E'}
    (h : (∀ e₁ e₂, G.cls e₁ ≠ none → G.cls e₂ ≠ none → g e₁ = g e₂ → e₁ = e₂) ∧
      Set.InjOn f (↑G.int ∪ ↑G.ext) ∧ G'.int = G.int.image f ∧ G'.ext = G.ext.image f ∧
      (∀ e, G.cls e ≠ none → G.IsVtx (G.ends e).1 ∧ G.IsVtx (G.ends e).2) ∧
      (∀ e, G.cls e ≠ none → G'.cls (g e) = G.cls e) ∧
      (∀ e, G.cls e ≠ none → G'.ends (g e) = (f (G.ends e).1, f (G.ends e).2) ∨
        G'.ends (g e) = (f (G.ends e).2, f (G.ends e).1)) ∧
      ∀ e', (∀ e, G.cls e ≠ none → g e ≠ e') → G'.cls e' = none) :
    Local_Carry G G' f := by
  obtain ⟨hg, hf, hint, hext, hv, hcl, he, hs⟩ := h
  have htr : G.Transported G' := ⟨f, g, hg, hf, hint, hext, hv, hcl, he, hs⟩
  intro hd hng hsp
  have hd' : Disjoint G'.int G'.ext := by
    rw [hint, hext, Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.1 hy'
    have hba : b = a := hf (by simp [hb]) (by simp [ha]) hab
    subst hba
    exact Finset.disjoint_left.1 hd ha hb
  have hng' : Local_NG G' := by
    intro e
    by_cases he' : ∃ e₀, G.cls e₀ ≠ none ∧ g e₀ = e
    · obtain ⟨e₀, he₀, rfl⟩ := he'
      rw [hcl e₀ he₀]
      exact hng e₀
    · rw [hs e (fun e₀ h₁ h₂ => he' ⟨e₀, h₁, h₂⟩)]
      simp
  refine ⟨(MGraph.spd_transport _ _ _ _ G G' htr).2 hsp, hng', hd', ?_⟩
  refine Local_pull_edgewise f g (fun v hv => by rw [hint]; exact Finset.mem_image_of_mem f hv)
    (fun w hw => by rw [hint] at hw; obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw; exact ⟨v, hv, rfl⟩)
    (fun v hv => by rw [hext]; exact Finset.mem_image_of_mem f hv) hsp.1 hd' (fun e hce _ => ?_)
    (fun e₁ e₂ c₁ c₂ _ _ h => hg e₁ e₂ c₁ c₂ h)
  rw [hcl e hce]
  exact ⟨hce, Iff.rfl, he e hce⟩

/-! ### The operations of `MGraph.CarStep` -/

section Steps

variable [DecidableEq V] [DecidableEq E]

/-- The `Local_Carry` conclusion from `MGraph.carStep_spd` and a `Local_Pull` argument. -/
private theorem Local_carry_step {G G' : MGraph V E} {φ : V → V} (h : MGraph.CarStep G G')
    (hp : Disjoint G'.int G'.ext → G.DC → G'.DC → Local_Pull G G' φ) : Local_Carry G G' φ := by
  intro hd hng hs
  obtain ⟨s', g', d'⟩ := MGraph.carStep_spd _ _ G G' h hd hng hs
  exact ⟨s', g', d', hp d' hs.1 s'.1⟩

/-- A blue loop added at an internal vertex carries the graph. -/
private theorem Local_carry_loop (G : MGraph V E) (e : E) (v : V) (he : G.cls e = none)
    (hv : v ∈ G.int) : Local_Carry G (G.setEdge e v v (some .plus)) id := by
  refine Local_carry_step (.loop G e v he hv) fun hd hdc _ => ?_
  refine Local_pull_edgewise id id (fun v hv => hv) (fun w hw => ⟨w, hw, rfl⟩) (fun v hv => hv) hdc
    hd (fun e₀ hce _ => ?_) (fun _ _ _ _ _ _ h => h)
  have h0 : e₀ ≠ e := by rintro rfl; exact hce he
  simp [MGraph.setEdge, h0, hce]

/-- Removing a loop carries the graph. -/
private theorem Local_carry_unloop (G : MGraph V E) (e : E) (he : G.cls e ≠ none)
    (hl : (G.ends e).1 = (G.ends e).2) : Local_Carry G (G.erase e) id := by
  refine Local_carry_step (.unloop G e he hl) fun hd hdc _ => ?_
  refine Local_pull_edgewise id id (fun v hv => hv) (fun w hw => ⟨w, hw, rfl⟩) (fun v hv => hv) hdc
    hd (fun e₀ hce hne => ?_) (fun _ _ _ _ _ _ h => h)
  have h0 : e₀ ≠ e := by rintro rfl; exact hne hl
  simp [MGraph.erase, h0, hce]

/-- `Local_Pull` for a path: the edge `e` from `a` to `b`, present and not red, replaced by the
edge `e` from `a` to the internal vertex `w` and the edge `e'` (absent before) from `w` to `b`, both
present and not red. -/
private theorem Local_pull_path {G G' : MGraph V E} {e e' : E} {w : V} (hee : e ≠ e')
    (hint : G'.int = G.int) (hext : G'.ext = G.ext) (hw : w ∈ G.int)
    (hce : G.cls e ≠ none ∧ G.cls e ≠ some .minus)
    (hce1 : G'.cls e ≠ none ∧ G'.cls e ≠ some .minus)
    (hce2 : G'.cls e' ≠ none ∧ G'.cls e' ≠ some .minus) (he' : G.cls e' = none)
    (hv : G.IsVtx (G.ends e).1 ∧ G.IsVtx (G.ends e).2)
    (hen1 : G'.ends e = ((G.ends e).1, w)) (hen2 : G'.ends e' = (w, (G.ends e).2))
    (hcl : ∀ f, f ≠ e → f ≠ e' → G'.cls f = G.cls f)
    (hen : ∀ f, f ≠ e → f ≠ e' → G'.ends f = G.ends f) (hdc : G.DC) :
    Local_Pull G G' id := by
  have hv' : ∀ v, G.IsVtx v → G'.IsVtx v := by
    intro v h
    simpa [MGraph.IsVtx, hint, hext] using h
  have hfil : ∀ P' : Finset V, P' ⊆ G'.int → G.int.filter (fun v => id v ∈ P') = P' := by
    intro P' hP'
    ext v
    simp only [Finset.mem_filter, id]
    exact ⟨fun h => h.2, fun h => ⟨hint ▸ hP' h, h⟩⟩
  refine Local_pull_of id (fun v h => hint ▸ h) (fun w hw => ⟨w, hint ▸ hw, rfl⟩) hdc
    fun P' hP'' => ?_
  have hP' : P' ⊆ G'.int := hP''.1.1
  rw [hfil P' hP']
  let g : E → E := fun f => if f = e then (if G'.Cut P' e then e else e') else f
  have hwv : G'.IsVtx w := Or.inl (hint ▸ hw)
  have gcr : ∀ f, G.Crosses P' f → G'.Crosses P' (g f) := by
    rintro f ⟨c1, c2, v1, v2, hcut⟩
    by_cases hfe : f = e
    · subst hfe
      simp only [g, if_true]
      by_cases hc : G'.Cut P' f
      · simp only [hc, if_true]
        exact ⟨hce1.1, hce1.2, by rw [hen1]; exact hv' _ v1, by rw [hen1]; exact hwv, hc⟩
      · simp only [hc, if_false]
        refine ⟨hce2.1, hce2.2, by rw [hen2]; exact hwv, by rw [hen2]; exact hv' _ v2, ?_⟩
        unfold MGraph.Cut at hc hcut ⊢
        rw [hen1] at hc
        rw [hen2]
        by_cases hwP : w ∈ P' <;> simp_all
    · have hfe' : f ≠ e' := by rintro rfl; exact c1 he'
      simp only [g, hfe, if_false]
      unfold MGraph.Cut at hcut
      exact ⟨by rw [hcl f hfe hfe']; exact c1, by rw [hcl f hfe hfe']; exact c2,
        by rw [hen f hfe hfe']; exact hv' _ v1, by rw [hen f hfe hfe']; exact hv' _ v2,
        by unfold MGraph.Cut; rw [hen f hfe hfe']; exact hcut⟩
  have ginj : ∀ f₁ f₂, G.cls f₁ ≠ none → G.cls f₂ ≠ none → g f₁ = g f₂ → f₁ = f₂ := by
    intro f₁ f₂ c₁ c₂ h
    have n₁ : f₁ ≠ e' := by rintro rfl; exact c₁ he'
    have n₂ : f₂ ≠ e' := by rintro rfl; exact c₂ he'
    by_cases h₁ : f₁ = e <;> by_cases h₂ : f₂ = e
    · rw [h₁, h₂]
    · simp only [g, h₁, h₂, if_true, if_false] at h
      split_ifs at h with hc
      · exact absurd h.symm h₂
      · exact absurd h.symm n₂
    · simp only [g, h₁, h₂, if_true, if_false] at h
      split_ifs at h with hc
      · exact absurd h h₁
      · exact absurd h n₁
    · simpa [g, h₁, h₂] using h
  refine ⟨g, gcr, fun f₁ f₂ c₁ c₂ h => ginj f₁ f₂ c₁.1 c₂.1 h, ?_, ?_⟩
  · rintro f ⟨r, v1, v2, hcut⟩
    have hfe : f ≠ e := by rintro rfl; exact hce.2 r
    have hfe' : f ≠ e' := by rintro rfl; rw [he'] at r; simp at r
    simp only [g, hfe, if_false]
    unfold MGraph.Cut at hcut
    exact ⟨by rw [hcl f hfe hfe']; exact r, by rw [hen f hfe hfe']; exact hv' _ v1,
      by rw [hen f hfe hfe']; exact hv' _ v2, by unfold MGraph.Cut; rw [hen f hfe hfe']; exact hcut⟩
  · rintro f₁ f₂ ⟨r₁, -⟩ ⟨r₂, -⟩ h
    exact ginj f₁ f₂ (by rw [r₁]; simp) (by rw [r₂]; simp) h

/-- Operation (B) carries the graph. -/
private theorem Local_carry_split (G : MGraph V E) (e e' : E) (w : V) (he : G.cls e = some .plus)
    (h1 : G.IsVtx (G.ends e).1) (h2 : G.IsVtx (G.ends e).2)
    (hi : (G.ends e).1 ∈ G.int ∨ (G.ends e).2 ∈ G.int) (hne : e ≠ e') (he' : G.cls e' = none)
    (hw : w ∈ G.int) : Local_Carry G (G.split e e' w) id := by
  refine Local_carry_step (.split G e e' w he h1 h2 hi hne he' hw) fun _ hdc _ => ?_
  have hne' : e' ≠ e := Ne.symm hne
  refine Local_pull_path hne rfl rfl hw (by rw [he]; simp) (by simp [MGraph.split, hne, he])
    (by simp [MGraph.split, he]) he' ⟨h1, h2⟩ (by simp [MGraph.split]) (by simp [MGraph.split, hne'])
    (fun f h h' => by simp [MGraph.split, h']) (fun f h h' => by simp [MGraph.split, h, h']) hdc

/-- `Local_Pull` for a red path: the edge `e` from `a` to `b`, red or absent, replaced by the
edge `e` from `a` to `w` and the edge `e'` (absent before) from `w` to `b`, each red when its ends
are distinct and absent otherwise. -/
private theorem Local_pull_redpath {G G' : MGraph V E} {e e' : E} {w : V} (hee : e ≠ e')
    (hint : G'.int = G.int) (hext : G'.ext = G.ext) (hwv : G.IsVtx w)
    (hce : G.cls e = none ∨ G.cls e = some .minus)
    (hce1 : G'.cls e = if (G.ends e).1 = w then none else some .minus)
    (hce2 : G'.cls e' = if w = (G.ends e).2 then none else some .minus) (he' : G.cls e' = none)
    (hv : G.cls e ≠ none → G.IsVtx (G.ends e).1 ∧ G.IsVtx (G.ends e).2)
    (hen1 : G'.ends e = ((G.ends e).1, w)) (hen2 : G'.ends e' = (w, (G.ends e).2))
    (hcl : ∀ f, f ≠ e → f ≠ e' → G'.cls f = G.cls f)
    (hen : ∀ f, f ≠ e → f ≠ e' → G'.ends f = G.ends f) (hdc : G.DC) :
    Local_Pull G G' id := by
  have hv' : ∀ v, G.IsVtx v → G'.IsVtx v := by
    intro v h
    simpa [MGraph.IsVtx, hint, hext] using h
  have hfil : ∀ P' : Finset V, P' ⊆ G'.int → G.int.filter (fun v => id v ∈ P') = P' := by
    intro P' hP'
    ext v
    simp only [Finset.mem_filter, id]
    exact ⟨fun h => h.2, fun h => ⟨hint ▸ hP' h, h⟩⟩
  have hnr1 : G'.cls e = none ∨ G'.cls e = some .minus := by
    rw [hce1]; split_ifs <;> simp
  have hnr2 : G'.cls e' = none ∨ G'.cls e' = some .minus := by
    rw [hce2]; split_ifs <;> simp
  refine Local_pull_of id (fun v h => hint ▸ h) (fun w hw => ⟨w, hint ▸ hw, rfl⟩) hdc
    fun P' hP'' => ?_
  have hP' : P' ⊆ G'.int := hP''.1.1
  rw [hfil P' hP']
  let g : E → E := fun f => if f = e then (if G'.Cut P' e then e else e') else f
  have gid : ∀ f, f ≠ e → g f = f := fun f h => by simp [g, h]
  have ginj : ∀ f₁ f₂, f₁ ≠ e' → f₂ ≠ e' → g f₁ = g f₂ → f₁ = f₂ := by
    intro f₁ f₂ n₁ n₂ h
    by_cases h₁ : f₁ = e <;> by_cases h₂ : f₂ = e
    · rw [h₁, h₂]
    · simp only [g, h₁, h₂, if_true, if_false] at h
      split_ifs at h with hc
      · exact absurd h.symm h₂
      · exact absurd h.symm n₂
    · simp only [g, h₁, h₂, if_true, if_false] at h
      split_ifs at h with hc
      · exact absurd h h₁
      · exact absurd h n₁
    · simpa [g, h₁, h₂] using h
  have ne' : ∀ f, G.cls f ≠ none → f ≠ e' := fun f h h' => h (h' ▸ he')
  refine ⟨g, ?_, fun f₁ f₂ c₁ c₂ h => ginj f₁ f₂ (ne' _ c₁.1) (ne' _ c₂.1) h, ?_,
    fun f₁ f₂ r₁ r₂ h => ginj f₁ f₂ (ne' _ (by rw [r₁.1]; simp))
      (ne' _ (by rw [r₂.1]; simp)) h⟩
  · rintro f ⟨c1, c2, v1, v2, hcut⟩
    have hfe : f ≠ e := by
      rintro rfl
      rcases hce with h | h
      · exact c1 h
      · exact c2 h
    have hfe' : f ≠ e' := ne' f c1
    rw [gid f hfe]
    unfold MGraph.Cut at hcut
    exact ⟨by rw [hcl f hfe hfe']; exact c1, by rw [hcl f hfe hfe']; exact c2,
      by rw [hen f hfe hfe']; exact hv' _ v1, by rw [hen f hfe hfe']; exact hv' _ v2,
      by unfold MGraph.Cut; rw [hen f hfe hfe']; exact hcut⟩
  · rintro f ⟨r, v1, v2, hcut⟩
    by_cases hfe : f = e
    · subst hfe
      simp only [g, if_true]
      by_cases hc : G'.Cut P' f
      · simp only [hc, if_true]
        have hne : (G.ends f).1 ≠ w := by
          intro h
          unfold MGraph.Cut at hc
          rw [hen1] at hc
          rcases hc with ⟨a, b⟩ | ⟨a, b⟩
          · exact b (h ▸ a)
          · exact a (h ▸ b)
        refine ⟨by rw [hce1]; simp [hne], by rw [hen1]; exact hv' _ v1, by rw [hen1]; exact hv' _ hwv,
          hc⟩
      · simp only [hc, if_false]
        unfold MGraph.Cut at hc hcut
        rw [hen1] at hc
        have hcut' : (w ∈ P' ∧ (G.ends f).2 ∉ P') ∨ (w ∉ P' ∧ (G.ends f).2 ∈ P') := by
          by_cases hwP : w ∈ P'
          · refine Or.inl ⟨hwP, ?_⟩
            rcases hcut with ⟨ha, hb⟩ | ⟨ha, hb⟩
            · exact hb
            · exact absurd (Or.inr ⟨ha, hwP⟩) hc
          · refine Or.inr ⟨hwP, ?_⟩
            rcases hcut with ⟨ha, hb⟩ | ⟨ha, hb⟩
            · exact absurd (Or.inl ⟨ha, hwP⟩) hc
            · exact hb
        have hne : w ≠ (G.ends f).2 := by
          intro h
          rcases hcut' with ⟨a, b⟩ | ⟨a, b⟩
          · exact b (h ▸ a)
          · exact a (h ▸ b)
        refine ⟨by rw [hce2]; simp [hne], by rw [hen2]; exact hv' _ hwv,
          by rw [hen2]; exact hv' _ v2, ?_⟩
        unfold MGraph.Cut
        rw [hen2]
        exact hcut'
    · have hfe' : f ≠ e' := ne' f (by rw [r]; simp)
      rw [gid f hfe]
      unfold MGraph.Cut at hcut
      exact ⟨by rw [hcl f hfe hfe']; exact r, by rw [hen f hfe hfe']; exact hv' _ v1,
        by rw [hen f hfe hfe']; exact hv' _ v2, by unfold MGraph.Cut; rw [hen f hfe hfe']; exact hcut⟩

/-- Two moves of red or absent edges (`MGraph.CarStep.red`) along a red path carry the graph. -/
private theorem Local_carry_redpath (G : MGraph V E) (e e' : E) (w : V) (hee : e ≠ e')
    (hwv : G.IsVtx w) (hce : G.cls e = none ∨ G.cls e = some .minus) (he' : G.cls e' = none)
    (hv : G.cls e ≠ none → G.IsVtx (G.ends e).1 ∧ G.IsVtx (G.ends e).2) :
    Local_Carry G ((G.setEdge e (G.ends e).1 w
        (if (G.ends e).1 = w then none else some .minus)).setEdge e' w (G.ends e).2
        (if w = (G.ends e).2 then none else some .minus)) id := by
  set c₁ : Option MClass := if (G.ends e).1 = w then none else some .minus
  set c₂ : Option MClass := if w = (G.ends e).2 then none else some .minus
  have hc₁ : c₁ = none ∨ c₁ = some .minus := by simp only [c₁]; split_ifs <;> simp
  have hc₂ : c₂ = none ∨ c₂ = some .minus := by simp only [c₂]; split_ifs <;> simp
  have hee' : e' ≠ e := Ne.symm hee
  have s₁ : MGraph.CarStep G (G.setEdge e (G.ends e).1 w c₁) := .red _ _ _ _ _ hce hc₁
  have s₂ : MGraph.CarStep (G.setEdge e (G.ends e).1 w c₁)
      ((G.setEdge e (G.ends e).1 w c₁).setEdge e' w (G.ends e).2 c₂) :=
    .red _ _ _ _ _ (Or.inl (by simp [MGraph.setEdge, hee', he'])) hc₂
  intro hd hng hs
  obtain ⟨sp₁, ng₁, d₁⟩ := MGraph.carStep_spd _ _ _ _ s₁ hd hng hs
  obtain ⟨sp₂, ng₂, d₂⟩ := MGraph.carStep_spd _ _ _ _ s₂ d₁ ng₁ sp₁
  refine ⟨sp₂, ng₂, d₂, Local_pull_redpath hee rfl rfl hwv hce (by simp [MGraph.setEdge, hee, c₁])
    (by simp [MGraph.setEdge, c₂]) he' hv (by simp [MGraph.setEdge, hee])
    (by simp [MGraph.setEdge]) (fun f h h' => by simp [MGraph.setEdge, h, h'])
    (fun f h h' => by simp [MGraph.setEdge, h, h']) hs.1⟩

/-- A molecular multigraph with the vertices and the classes of the edges of `H`, and the ends of
the present edges of `H`, is carried onto `H` by the identity. -/
private theorem Local_carry_agree (G H : MGraph V E) (hi : G.int = H.int)
    (he : G.ext = H.ext) (hc : ∀ e, G.cls e = H.cls e)
    (hn : ∀ e, H.cls e ≠ none → G.ends e = H.ends e)
    (hv : ∀ e, H.cls e ≠ none → H.IsVtx (H.ends e).1 ∧ H.IsVtx (H.ends e).2) :
    Local_Carry G H id := by
  refine Local_carry_tr (g := id) ⟨fun _ _ _ _ h => h, Set.injOn_id _, by rw [hi, Finset.image_id],
    by rw [he, Finset.image_id], fun e h => ?_, fun e _ => (hc e).symm,
    fun e h => Or.inl ?_, fun e' h' => ?_⟩
  · rw [hc] at h
    rw [hn e h]
    simp only [MGraph.IsVtx, hi, he]
    exact hv e h
  · rw [hc] at h
    rw [hn e h]
    rfl
  · by_contra hne
    exact h' e' (by rw [hc]; exact hne) rfl

/-- The operations (B) and (Loop) on the path `A – X – B`, or two moves of red edges: an edge `s₁`
from `A` to `B` of class `m` (absent if `A = B`) and an absent edge `s₂` become the edges `s₁` from
`A` to `X` and `s₂` from `X` to `B` of class `m` (each absent if its ends are equal), for a blue or
red class `m`, with `A` and `X` internal. -/
private theorem Local_carry_chain (H : MGraph V E) (s₁ s₂ : E)
    (hs : s₁ ≠ s₂) (A B X : V) (m : MClass) (hm : m = .plus ∨ m = .minus)
    (hA : A ∈ H.int) (hB : H.IsVtx B) (hX : X ∈ H.int)
    (h₁ : H.ends s₁ = (A, X)) (h₁c : H.cls s₁ = if A = X then none else some m)
    (h₂ : H.ends s₂ = (X, B)) (h₂c : H.cls s₂ = if X = B then none else some m) :
    ∃ G₁, Local_Carry ((H.erase s₂).setEdge s₁ A B (if A = B then none else some m)) G₁ id ∧
      G₁.int = H.int ∧ G₁.ext = H.ext ∧ (∀ e, G₁.cls e = H.cls e) ∧
      ∀ e, H.cls e ≠ none → G₁.ends e = H.ends e := by
  have hs' : s₂ ≠ s₁ := fun h => hs h.symm
  have refl0 : ∀ K : MGraph V E, Local_Carry K K id := fun K hd hng hsp =>
    ⟨hsp, hng, hd, Local_pull_id K⟩
  rcases hm with rfl | rfl
  · by_cases hAB : A = B
    · subst hAB
      by_cases hAX : A = X
      · subst hAX
        refine ⟨_, refl0 _, rfl, rfl, fun e => ?_, fun e he => ?_⟩
        · by_cases e1 : e = s₁
          · subst e1; simp [MGraph.setEdge, h₁c]
          · by_cases e2 : e = s₂
            · subst e2; simp [MGraph.setEdge, MGraph.erase, h₂c, hs']
            · simp [MGraph.setEdge, MGraph.erase, e1, e2]
        · have e1 : e ≠ s₁ := by rintro rfl; simp [h₁c] at he
          simp [MGraph.setEdge, MGraph.erase, e1]
      · refine ⟨_, Local_carry_trans_id (Local_carry_loop ((H.erase s₂).setEdge s₁ A A
            (if A = A then none else some .plus)) s₁ A (by simp [MGraph.setEdge]) hA)
          (Local_carry_split _ s₁ s₂ X (by simp [MGraph.setEdge])
            (by simp [MGraph.setEdge, MGraph.IsVtx, hA])
            (by simp [MGraph.setEdge, MGraph.IsVtx, hA]) (by simp [MGraph.setEdge, hA]) hs
            (by simp [MGraph.setEdge, MGraph.erase, hs']) hX), rfl, rfl, fun e => ?_,
          fun e _ => ?_⟩
        · by_cases e1 : e = s₂
          · subst e1; simp [MGraph.split, MGraph.setEdge, h₂c, Ne.symm hAX]
          · by_cases e2 : e = s₁
            · subst e2; simp [MGraph.split, MGraph.setEdge, h₁c, hAX, hs]
            · simp [MGraph.split, MGraph.setEdge, MGraph.erase, e1, e2]
        · by_cases e1 : e = s₁
          · subst e1; simp [MGraph.split, MGraph.setEdge, h₁]
          · by_cases e2 : e = s₂
            · subst e2; simp [MGraph.split, MGraph.setEdge, h₂, hs']
            · simp [MGraph.split, MGraph.setEdge, MGraph.erase, e1, e2]
    · have hsp := Local_carry_split ((H.erase s₂).setEdge s₁ A B
          (if A = B then none else some .plus)) s₁ s₂ X (by simp [MGraph.setEdge, hAB])
          (by simp [MGraph.setEdge, MGraph.IsVtx, hA])
          (by simpa [MGraph.setEdge, MGraph.IsVtx] using hB) (by simp [MGraph.setEdge, hA]) hs
          (by simp [MGraph.setEdge, MGraph.erase, hs']) hX
      by_cases hXA : X = A
      · subst hXA
        refine ⟨_, Local_carry_trans_id hsp
          (Local_carry_unloop _ s₁ (by simp [MGraph.split, MGraph.setEdge, hAB, hs])
            (by simp [MGraph.split, MGraph.setEdge])), rfl, rfl, fun e => ?_, fun e he => ?_⟩
        · by_cases e1 : e = s₁
          · subst e1; simp [MGraph.erase, h₁c]
          · by_cases e2 : e = s₂
            · subst e2; simp [MGraph.erase, MGraph.split, MGraph.setEdge, h₂c, hAB, hs']
            · simp [MGraph.erase, MGraph.split, MGraph.setEdge, e1, e2]
        · have e1 : e ≠ s₁ := by rintro rfl; simp [h₁c] at he
          by_cases e2 : e = s₂
          · subst e2; simp [MGraph.erase, MGraph.split, MGraph.setEdge, h₂, hs']
          · simp [MGraph.erase, MGraph.split, MGraph.setEdge, e1, e2]
      · by_cases hXB : X = B
        · subst hXB
          refine ⟨_, Local_carry_trans_id hsp (Local_carry_unloop _ s₂
            (by simp [MGraph.split, MGraph.setEdge, hAB])
            (by simp [MGraph.split, MGraph.setEdge, hs'])), rfl, rfl, fun e => ?_, fun e he => ?_⟩
          · by_cases e1 : e = s₂
            · subst e1; simp [MGraph.erase, h₂c]
            · by_cases e2 : e = s₁
              · subst e2; simp [MGraph.erase, MGraph.split, MGraph.setEdge, h₁c, hAB, hs]
              · simp [MGraph.erase, MGraph.split, MGraph.setEdge, e1, e2]
          · have e1 : e ≠ s₂ := by rintro rfl; simp [h₂c] at he
            by_cases e2 : e = s₁
            · subst e2; simp [MGraph.erase, MGraph.split, MGraph.setEdge, h₁]
            · simp [MGraph.erase, MGraph.split, MGraph.setEdge, e1, e2]
        · refine ⟨_, hsp, rfl, rfl, fun e => ?_, fun e _ => ?_⟩
          · by_cases e1 : e = s₂
            · subst e1; simp [MGraph.split, MGraph.setEdge, h₂c, hAB, hXB]
            · by_cases e2 : e = s₁
              · subst e2; simp [MGraph.split, MGraph.setEdge, h₁c, hAB, Ne.symm hXA, hs]
              · simp [MGraph.split, MGraph.setEdge, MGraph.erase, e1, e2]
          · by_cases e1 : e = s₁
            · subst e1; simp [MGraph.split, MGraph.setEdge, h₁]
            · by_cases e2 : e = s₂
              · subst e2; simp [MGraph.split, MGraph.setEdge, h₂, hs']
              · simp [MGraph.split, MGraph.setEdge, MGraph.erase, e1, e2]
  · have hc := Local_carry_redpath ((H.erase s₂).setEdge s₁ A B
        (if A = B then none else some .minus)) s₁ s₂ X hs (Or.inl (by simp [MGraph.setEdge, hX]))
      (by simp only [MGraph.setEdge, Function.update_self]; split_ifs <;> simp)
      (by simp [MGraph.setEdge, MGraph.erase, hs'])
      (fun _ => by simpa [MGraph.setEdge, MGraph.IsVtx, hA] using hB)
    refine ⟨_, hc, rfl, rfl, fun e => ?_, fun e _ => ?_⟩
    · by_cases e1 : e = s₂
      · subst e1; simp [MGraph.setEdge, h₂c]
      · by_cases e2 : e = s₁
        · subst e2; simp [MGraph.setEdge, h₁c, hs]
        · simp [MGraph.setEdge, MGraph.erase, e1, e2]
    · by_cases e1 : e = s₂
      · subst e1; simp [MGraph.setEdge, h₂]
      · by_cases e2 : e = s₁
        · subst e2; simp [MGraph.setEdge, h₁, hs]
        · simp [MGraph.setEdge, MGraph.erase, e1, e2]

end Steps

/-- Two graphs whose edges `.inl` are matched by a cast of the positions, with the same vertices,
classes and ends of the present edges: carried by the identity. -/
private theorem Local_carry_cast {V Pn : Type} [DecidableEq V] [DecidableEq Pn] {m m' : ℕ}
    (h : m = m') (G : MGraph V (Fin m ⊕ Pn)) (G' : MGraph V (Fin m' ⊕ Pn)) (hi : G'.int = G.int)
    (hx : G'.ext = G.ext) (hc : ∀ i : Fin m, G'.cls (.inl (Fin.cast h i)) = G.cls (.inl i))
    (hcp : ∀ a, G'.cls (.inr a) = G.cls (.inr a))
    (he : ∀ i : Fin m, G.cls (.inl i) ≠ none → G'.ends (.inl (Fin.cast h i)) = G.ends (.inl i))
    (hep : ∀ a, G.cls (.inr a) ≠ none → G'.ends (.inr a) = G.ends (.inr a))
    (hv : ∀ e, G.cls e ≠ none → G.IsVtx (G.ends e).1 ∧ G.IsVtx (G.ends e).2) :
    Local_Carry G G' id := by
  refine Local_carry_tr (g := Sum.map (Fin.cast h) id) ⟨?_, Set.injOn_id _, by rw [hi,
    Finset.image_id], by rw [hx, Finset.image_id], hv, ?_, ?_, ?_⟩
  · rintro (i | a) (j | b) _ _ hij
    · simp only [Sum.map_inl, Sum.inl.injEq] at hij
      exact congrArg Sum.inl (Fin.cast_injective h hij)
    · simp at hij
    · simp at hij
    · simpa using hij
  · rintro (i | a) _
    · exact hc i
    · exact hcp a
  · rintro (i | a) hne
    · exact Or.inl (he i hne)
    · exact Or.inl (hep a hne)
  · rintro (j | a) hj
    · have := hj (.inl (Fin.cast h.symm j))
      simp only [Sum.map_inl, Fin.cast_cast, Fin.cast_eq_self, ne_eq, not_true_eq_false,
        imp_false, not_not] at this
      rw [← this, ← hc]
      simp
    · have := hj (.inr a)
      simp only [Sum.map_inr, id, ne_eq, not_true_eq_false, imp_false, not_not] at this
      rw [hcp, this]


end Carry

section ELG

variable {V Pn : Type} [DecidableEq Pn]

/-- An entry of a list of edges: a class (`none` for an absent edge) and a pair of ends. -/
private abbrev Local_Ed (V : Type) : Type := Option MClass × V × V

/-- The molecular multigraph with the internal vertices `I`, the external vertices `X`, the edge
`.inr a` given by `pe a` and the edge `.inl i` given by the entry `i` of `L`. -/
private def Local_ELG (I X : Finset V) (pe : Pn → Local_Ed V) (L : List (Local_Ed V)) :
    MGraph V (Fin L.length ⊕ Pn) where
  int := I
  ext := X
  ends e := match e with
    | .inl i => L[i].2
    | .inr a => (pe a).2
  cls e := match e with
    | .inl i => L[i].1
    | .inr a => (pe a).1

/-- A present entry joins vertices. -/
private def Local_VOK (I X : Finset V) (e : Local_Ed V) : Prop :=
  e.1 ≠ none → (e.2.1 ∈ I ∨ e.2.1 ∈ X) ∧ (e.2.2 ∈ I ∨ e.2.2 ∈ X)

/-- Two entries are the same edge: both absent, or of the same class with the same pair of ends
in either order. -/
private def Local_Same (e e' : Local_Ed V) : Prop :=
  (e.1 = none ∧ e'.1 = none) ∨ (e'.1 = e.1 ∧ (e'.2 = e.2 ∨ e'.2 = e.2.swap))

private theorem Local_Same.refl (e : Local_Ed V) : Local_Same e e := Or.inr ⟨rfl, Or.inl rfl⟩

/-- The present edges `.inl` of a graph of a list of edges join vertices. -/
private theorem Local_ELG_vok_inl {I X : Finset V} {pe : Pn → Local_Ed V} (L : List (Local_Ed V))
    (hv : ∀ e ∈ L, Local_VOK I X e) (i : Fin L.length)
    (h : (Local_ELG I X pe L).cls (.inl i) ≠ none) :
    (Local_ELG I X pe L).IsVtx ((Local_ELG I X pe L).ends (.inl i)).1 ∧
      (Local_ELG I X pe L).IsVtx ((Local_ELG I X pe L).ends (.inl i)).2 :=
  hv _ (List.getElem_mem _) h

/-- The criterion for a change of names between two graphs of lists of edges with the same
vertices: a map of the positions, injective on the present entries, sending them to the same edges
of the second list, and onto its present entries. -/
private theorem Local_ELG_tr [DecidableEq V] {I X : Finset V} {pe pe' : Pn → Local_Ed V}
    {L L' : List (Local_Ed V)} (g : Fin L.length → Fin L'.length ⊕ Pn)
    (hinj : ∀ i j : Fin L.length, L[i].1 ≠ none → L[j].1 ≠ none → g i = g j → i = j)
    (hval : ∀ i : Fin L.length, L[i].1 ≠ none → ∃ j : Fin L'.length, g i = .inl j ∧
      Local_Same L[i] L'[j])
    (hcov : ∀ j : Fin L'.length, L'[j].1 ≠ none → ∃ i : Fin L.length, L[i].1 ≠ none ∧ g i = .inl j)
    (hpin : ∀ a, Local_Same (pe a) (pe' a))
    (hv : ∀ i : Fin L.length, Local_VOK I X L[i]) (hvp : ∀ a, Local_VOK I X (pe a)) :
    Local_Carry (Local_ELG I X pe L) (Local_ELG I X pe' L') id := by
  refine Local_carry_tr (g := Sum.elim g .inr) ⟨?_, Set.injOn_id _, Finset.image_id.symm,
    Finset.image_id.symm, ?_, ?_, ?_, ?_⟩
  · rintro (i | a) (j | b) h1 h2 h
    · simp only [Sum.elim_inl] at h
      rw [hinj i j h1 h2 h]
    · obtain ⟨j', hj', -⟩ := hval i h1
      simp only [Sum.elim_inl, Sum.elim_inr, hj'] at h
      exact absurd h (by simp)
    · obtain ⟨j', hj', -⟩ := hval j h2
      simp only [Sum.elim_inl, Sum.elim_inr, hj'] at h
      exact absurd h (by simp)
    · simpa using h
  · rintro (i | a) h
    · exact hv i h
    · exact hvp a h
  · rintro (i | a) h
    · obtain ⟨j, hj, hs⟩ := hval i h
      simp only [Sum.elim_inl, hj]
      rcases hs with ⟨h', -⟩ | ⟨h', -⟩
      · exact absurd h' h
      · exact h'
    · rcases hpin a with ⟨h', -⟩ | ⟨h', -⟩
      · exact absurd h' h
      · exact h'
  · rintro (i | a) h
    · obtain ⟨j, hj, hs⟩ := hval i h
      simp only [Sum.elim_inl, hj]
      rcases hs with ⟨h', -⟩ | ⟨-, h' | h'⟩
      · exact absurd h' h
      · left
        change L'[j].2 = _
        rw [h']
        rfl
      · right
        change L'[j].2 = _
        rw [h']
        rfl
    · rcases hpin a with ⟨h', -⟩ | ⟨-, h' | h'⟩
      · exact absurd h' h
      · left
        change (pe' a).2 = _
        rw [h']
        rfl
      · right
        change (pe' a).2 = _
        rw [h']
        rfl
  · rintro (j | a) h
    · by_contra hc
      obtain ⟨i, hi, hgi⟩ := hcov j hc
      exact h (.inl i) hi (by simp [hgi])
    · by_contra hc
      have : (pe a).1 ≠ none := by
        rcases hpin a with ⟨-, h'⟩ | ⟨h', -⟩
        · exact absurd h' hc
        · rw [← h']; exact hc
      exact h (.inr a) this rfl

/-- A permutation of the entries is a change of names. -/
private theorem Local_ELG_perm [DecidableEq V] {I X : Finset V} {pe : Pn → Local_Ed V}
    {L L' : List (Local_Ed V)} (h : L.Perm L') (hv : ∀ e ∈ L, Local_VOK I X e)
    (hvp : ∀ a, Local_VOK I X (pe a)) :
    Local_Carry (Local_ELG I X pe L) (Local_ELG I X pe L') id := by
  obtain ⟨g, hg, hval⟩ := Local_perm_fin h
  refine Local_ELG_tr (fun i => .inl (g i)) (fun i j _ _ h => hg.1 (Sum.inl_injective h))
    (fun i _ => ⟨g i, rfl, by rw [hval]; exact Local_Same.refl _⟩) (fun j hj => ?_)
    (fun a => Local_Same.refl _) (fun i => hv _ (List.getElem_mem _)) hvp
  obtain ⟨i, rfl⟩ := hg.2 j
  refine ⟨i, ?_, rfl⟩
  rw [hval] at hj
  exact hj

/-- Entries replaced one by one by the same edges: a change of names. -/
private theorem Local_ELG_same [DecidableEq V] {I X : Finset V} {pe pe' : Pn → Local_Ed V}
    {L L' : List (Local_Ed V)} (h : List.Forall₂ Local_Same L L')
    (hpin : ∀ a, Local_Same (pe a) (pe' a))
    (hv : ∀ e ∈ L, Local_VOK I X e) (hvp : ∀ a, Local_VOK I X (pe a)) :
    Local_Carry (Local_ELG I X pe L) (Local_ELG I X pe' L') id := by
  have hlen := h.length_eq
  have hget : ∀ (i : ℕ) (h1 : i < L.length) (h2 : i < L'.length), Local_Same L[i] L'[i] := by
    intro i h1 h2
    exact (List.forall₂_iff_get.1 h).2 i h1 h2
  refine Local_ELG_tr (fun i => .inl (Fin.cast hlen i))
    (fun i j _ _ h => by simpa [Fin.ext_iff] using h)
    (fun i _ => ⟨Fin.cast hlen i, rfl, hget i i.2 _⟩)
    (fun j hj => ⟨Fin.cast hlen.symm j, ?_, by simp⟩) hpin
    (fun i => hv _ (List.getElem_mem _)) hvp
  have := hget j (by omega) j.2
  rcases this with ⟨-, h'⟩ | ⟨h', -⟩
  · exact absurd h' hj
  · simpa [← h'] using hj

/-- Absent entries appended: a change of names. -/
private theorem Local_ELG_append_none [DecidableEq V] {I X : Finset V} {pe : Pn → Local_Ed V}
    {L A : List (Local_Ed V)} (hA : ∀ e ∈ A, e.1 = none) (hv : ∀ e ∈ L, Local_VOK I X e)
    (hvp : ∀ a, Local_VOK I X (pe a)) :
    Local_Carry (Local_ELG I X pe L) (Local_ELG I X pe (L ++ A)) id := by
  refine Local_ELG_tr (fun i => .inl ⟨i, by simp; omega⟩)
    (fun i j _ _ h => by simpa [Fin.ext_iff] using h)
    (fun i _ => ⟨_, rfl, ?_⟩) (fun j hj => ?_) (fun a => Local_Same.refl _)
    (fun i => hv _ (List.getElem_mem _)) hvp
  · simp only [Fin.getElem_fin, List.getElem_append_left i.2]
    exact Local_Same.refl _
  · by_cases hjL : (j : ℕ) < L.length
    · refine ⟨⟨j, hjL⟩, ?_, rfl⟩
      simp only [Fin.getElem_fin] at hj ⊢
      rwa [List.getElem_append_left hjL] at hj
    · exfalso
      simp only [Fin.getElem_fin] at hj
      rw [List.getElem_append_right (by omega)] at hj
      exact hj (hA _ (List.getElem_mem _))

/-- Absent entries removed from the end: a change of names. -/
private theorem Local_ELG_drop_none [DecidableEq V] {I X : Finset V} {pe : Pn → Local_Ed V}
    (a₀ : Pn) {L A : List (Local_Ed V)} (hA : ∀ e ∈ A, e.1 = none)
    (hv : ∀ e ∈ L, Local_VOK I X e) (hvp : ∀ a, Local_VOK I X (pe a)) :
    Local_Carry (Local_ELG I X pe (L ++ A)) (Local_ELG I X pe L) id := by
  have hpres : ∀ i : Fin (L ++ A).length, (L ++ A)[i].1 ≠ none → (i : ℕ) < L.length := by
    intro i hi
    by_contra hc
    simp only [Fin.getElem_fin] at hi
    rw [List.getElem_append_right (by omega)] at hi
    exact hi (hA _ (List.getElem_mem _))
  refine Local_ELG_tr (fun i => if h : (i : ℕ) < L.length then .inl ⟨i, h⟩ else .inr a₀)
    (fun i j hi hj h => ?_) (fun i hi => ⟨⟨i, hpres i hi⟩, by simp [hpres i hi], ?_⟩)
    (fun j hj => ⟨⟨j, by simp; omega⟩, ?_, by simp [j.2]⟩)
    (fun a => Local_Same.refl _) (fun i => ?_) hvp
  · simp only [hpres i hi, hpres j hj, dite_true, Sum.inl.injEq, Fin.mk.injEq] at h
    exact Fin.ext h
  · simp only [Fin.getElem_fin, List.getElem_append_left (hpres i hi)]
    exact Local_Same.refl _
  · simp only [Fin.getElem_fin, List.getElem_append_left j.2]
    exact hj
  · by_cases hi : (i : ℕ) < L.length
    · simp only [Fin.getElem_fin, List.getElem_append_left hi]
      exact hv _ (List.getElem_mem _)
    · simp only [Fin.getElem_fin]
      rw [List.getElem_append_right (by omega)]
      intro h
      exact absurd (hA _ (List.getElem_mem _)) h

/-- The entry of a path step: the class `m` between distinct ends, absent between equal ends. -/
private def Local_pe {V : Type} [DecidableEq V] (m : MClass) (A B : V) : Local_Ed V :=
  (if A = B then none else some m, A, B)

/-- One entry from `A` to `B` replaced by the entries from `A` to `X` and from `X` to `B`, of a blue
or red class (absent between equal ends), with `A` and `X` internal: carried by the identity. -/
private theorem Local_ELG_path [DecidableEq V] {I X₀ : Finset V} {pe : Pn → Local_Ed V}
    {L₀ : List (Local_Ed V)} {A B X : V} {m : MClass} (hm : m = .plus ∨ m = .minus)
    (hA : A ∈ I) (hX : X ∈ I) (hB : B ∈ I ∨ B ∈ X₀)
    (hv : ∀ e ∈ L₀, Local_VOK I X₀ e) (hvp : ∀ a, Local_VOK I X₀ (pe a)) :
    Local_Carry (Local_ELG I X₀ pe (L₀ ++ [Local_pe m A B]))
      (Local_ELG I X₀ pe (L₀ ++ [Local_pe m A X, Local_pe m X B])) id := by
  set H := Local_ELG I X₀ pe (L₀ ++ [Local_pe m A X, Local_pe m X B]) with hH
  have hlen : (L₀ ++ [Local_pe m A X, Local_pe m X B]).length = L₀.length + 2 := by simp
  let s₁ : Fin (L₀ ++ [Local_pe m A X, Local_pe m X B]).length := ⟨L₀.length, by omega⟩
  let s₂ : Fin (L₀ ++ [Local_pe m A X, Local_pe m X B]).length := ⟨L₀.length + 1, by omega⟩
  have g₁ : (L₀ ++ [Local_pe m A X, Local_pe m X B])[s₁] = Local_pe m A X := by
    simp [s₁]
  have g₂ : (L₀ ++ [Local_pe m A X, Local_pe m X B])[s₂] = Local_pe m X B := by
    simp [s₂]
  have h12 : (Sum.inl s₁ : Fin _ ⊕ Pn) ≠ .inl s₂ := by simp [s₁, s₂]
  obtain ⟨G₁, hch, hG₁i, hG₁e, hG₁c, hG₁n⟩ := Local_carry_chain H (.inl s₁) (.inl s₂) h12 A B X m
    hm hA hB hX (by change (L₀ ++ _)[s₁].2 = _; rw [g₁]; rfl)
    (by change (L₀ ++ _)[s₁].1 = _; rw [g₁]; rfl)
    (by change (L₀ ++ _)[s₂].2 = _; rw [g₂]; rfl)
    (by change (L₀ ++ _)[s₂].1 = _; rw [g₂]; rfl)
  have hvH : ∀ e ∈ L₀ ++ [Local_pe m A X, Local_pe m X B], Local_VOK I X₀ e := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact hv e he
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact fun _ => ⟨Or.inl hA, Or.inl hX⟩
      · exact fun _ => ⟨Or.inl hX, hB⟩
  have hagree := Local_carry_agree G₁ H hG₁i hG₁e hG₁c hG₁n (fun e he => by
    rcases e with i | a
    · exact Local_ELG_vok_inl _ hvH i he
    · exact hvp a he)
  -- the first graph, with one absent entry appended, is `G₀`
  have happ := Local_ELG_append_none (I := I) (X := X₀) (pe := pe) (L := L₀ ++ [Local_pe m A B])
    (A := [(none, X, B)]) (by simp) (fun e he => by
      rcases List.mem_append.1 he with he | he
      · exact hv e he
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        subst he
        exact fun _ => ⟨Or.inl hA, hB⟩) hvp
  have hlen' : (L₀ ++ [Local_pe m A B] ++ [((none : Option MClass), X, B)]).length =
      (L₀ ++ [Local_pe m A X, Local_pe m X B]).length := by simp
  have hcast := Local_carry_cast hlen' (Local_ELG I X₀ pe (L₀ ++ [Local_pe m A B] ++ [(none, X, B)]))
    ((H.erase (.inl s₂)).setEdge (.inl s₁) A B (if A = B then none else some m)) rfl rfl
    (fun i => ?_) (fun a => ?_) (fun i hi => ?_) (fun a _ => ?_) (fun e he => ?_)
  · exact Local_carry_trans_id (Local_carry_trans_id happ hcast) (Local_carry_trans_id hch hagree)
  · -- classes of the edges `.inl`
    obtain ⟨i, hi⟩ := i
    have hi' : i < L₀.length + 2 := by simpa using hi
    by_cases h1 : i = L₀.length
    · subst h1
      have e : Fin.cast hlen' ⟨L₀.length, hi⟩ = s₁ := Fin.ext rfl
      rw [e]
      simp only [MGraph.setEdge, Function.update_self]
      simp [Local_ELG, Local_pe]
    · by_cases h2 : i = L₀.length + 1
      · subst h2
        have e : Fin.cast hlen' ⟨L₀.length + 1, hi⟩ = s₂ := Fin.ext rfl
        rw [e]
        simp only [MGraph.setEdge, MGraph.erase]
        rw [Function.update_of_ne (Ne.symm h12), Function.update_self]
        simp [Local_ELG, List.getElem_append_right]
      · have hiL : i < L₀.length := by omega
        have e1 : (Sum.inl (Fin.cast hlen' ⟨i, hi⟩) : Fin _ ⊕ Pn) ≠ .inl s₁ := by
          simp [s₁, Fin.ext_iff, h1]
        have e2 : (Sum.inl (Fin.cast hlen' ⟨i, hi⟩) : Fin _ ⊕ Pn) ≠ .inl s₂ := by
          simp [s₂, Fin.ext_iff, h2]
        simp only [MGraph.setEdge, MGraph.erase]
        rw [Function.update_of_ne e1, Function.update_of_ne e2]
        simp [H, Local_ELG, List.getElem_append_left hiL]
  · simp [MGraph.setEdge, MGraph.erase, H, Local_ELG, Function.update]
  · -- ends of the present edges `.inl`
    obtain ⟨i, hi'⟩ := i
    have hi'' : i < L₀.length + 2 := by simpa using hi'
    by_cases h1 : i = L₀.length
    · subst h1
      have e : Fin.cast hlen' ⟨L₀.length, hi'⟩ = s₁ := Fin.ext rfl
      rw [e]
      simp [MGraph.setEdge, Local_ELG, Local_pe]
    · by_cases h2 : i = L₀.length + 1
      · subst h2
        exfalso
        apply hi
        simp [Local_ELG, List.getElem_append_right]
      · have hiL : i < L₀.length := by omega
        have e1 : (Sum.inl (Fin.cast hlen' ⟨i, hi'⟩) : Fin _ ⊕ Pn) ≠ .inl s₁ := by
          simp [s₁, Fin.ext_iff, h1]
        simp only [MGraph.setEdge, MGraph.erase]
        rw [if_neg e1]
        simp [H, Local_ELG, List.getElem_append_left hiL]
  · simp [MGraph.setEdge, MGraph.erase, H, Local_ELG]
  · rcases e with i | a
    · exact Local_ELG_vok_inl _ (fun e he => by
        rcases List.mem_append.1 he with he | he
        · rcases List.mem_append.1 he with he | he
          · exact hv e he
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
            subst he
            exact fun _ => ⟨Or.inl hA, hB⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          subst he
          exact fun h => absurd rfl h) i he
    · exact hvp a he

/-- The entry with its ends mapped by `F`. -/
private def Local_edMap {V V' : Type} (F : V → V') (e : Local_Ed V) : Local_Ed V' :=
  (e.1, F e.2.1, F e.2.2)

/-- All entries and vertices mapped by a map injective on the vertices: carried along the map. -/
private theorem Local_ELG_mapV {V' : Type} [DecidableEq V] [DecidableEq V'] {I X : Finset V}
    {pe : Pn → Local_Ed V} {pe' : Pn → Local_Ed V'} (F : V → V') (L : List (Local_Ed V))
    (hF : Set.InjOn F (↑I ∪ ↑X)) (hpin : ∀ a, Local_Same (Local_edMap F (pe a)) (pe' a))
    (hv : ∀ e ∈ L, Local_VOK I X e) (hvp : ∀ a, Local_VOK I X (pe a)) :
    Local_Carry (Local_ELG I X pe L) (Local_ELG (I.image F) (X.image F) pe'
      (L.map (Local_edMap F))) F := by
  have hlen : (L.map (Local_edMap F)).length = L.length := by simp
  refine Local_carry_tr (g := Sum.map (Fin.cast hlen.symm) id) ⟨?_, hF, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rintro (i | a) (i' | a') _ _ hh
    · simp only [Sum.map_inl, Sum.inl.injEq] at hh
      exact congrArg Sum.inl (Fin.cast_injective _ hh)
    · simp at hh
    · simp at hh
    · simpa using hh
  · rintro (i | a) he
    · exact Local_ELG_vok_inl _ hv i he
    · exact hvp a he
  · rintro (i | a) he
    · simp [Local_ELG, Local_edMap]
    · rcases hpin a with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 he
      · simp only [Sum.map_inr, id, Local_ELG]
        rw [h1]
        rfl
  · rintro (i | a) he
    · left
      simp [Local_ELG, Local_edMap]
    · rcases hpin a with ⟨h1, -⟩ | ⟨-, h2 | h2⟩
      · exact absurd h1 he
      · left
        change (pe' a).2 = _
        rw [h2]
        rfl
      · right
        change (pe' a).2 = _
        rw [h2]
        rfl
  · rintro (i | a) hh
    · have := hh (.inl (Fin.cast hlen i))
      simp only [Sum.map_inl, Fin.cast_cast, Fin.cast_eq_self, ne_eq, not_true_eq_false,
        imp_false, not_not] at this
      simpa [Local_ELG, Local_edMap] using this
    · have := hh (.inr a)
      simp only [Sum.map_inr, id, ne_eq, not_true_eq_false, imp_false, not_not] at this
      rcases hpin a with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2
      · change (pe' a).1 = none
        rw [h1]
        exact this

/-- A list of entries read from a list `cs`, and the entries of the elements kept by `ψ` (an
element dropped by `ψ` reads absent, a kept one reads the same edge): carried by the identity. -/
private theorem Local_ELG_filterMap' [DecidableEq V] {α β : Type} (a₀ : Pn) {I X : Finset V}
    {pe pe' : Pn → Local_Ed V} (cs : List α) (g₁ : α → Local_Ed V) (ψ : α → Option β)
    (g₂ : β → Local_Ed V)
    (hψ : ∀ c ∈ cs, (ψ c = none → (g₁ c).1 = none) ∧
      ∀ c', ψ c = some c' → Local_Same (g₁ c) (g₂ c'))
    (hpin : ∀ a, Local_Same (pe a) (pe' a))
    (hv : ∀ c ∈ cs, Local_VOK I X (g₁ c)) (hvp : ∀ a, Local_VOK I X (pe a)) :
    Local_Carry (Local_ELG I X pe (cs.map g₁)) (Local_ELG I X pe' ((cs.filterMap ψ).map g₂)) id := by
  have hperm := (List.filter_append_perm (fun c => (ψ c).isSome) cs).map g₁
  rw [List.map_append] at hperm
  have hv' : ∀ e ∈ cs.map g₁, Local_VOK I X e := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
    exact hv c hc
  have h1 := Local_ELG_perm (pe := pe) hperm.symm hv' hvp
  have h2 : Local_Carry (Local_ELG I X pe ((cs.filter (fun c => (ψ c).isSome)).map g₁ ++
      (cs.filter (fun c => !(ψ c).isSome)).map g₁))
      (Local_ELG I X pe ((cs.filter (fun c => (ψ c).isSome)).map g₁)) id :=
    Local_ELG_drop_none a₀ (fun e he => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
      obtain ⟨hc, hn⟩ := List.mem_filter.1 hc
      exact (hψ c hc).1 (by simpa using hn)) (fun e he => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
      exact hv c (List.mem_filter.1 hc).1) hvp
  have hf2 : List.Forall₂ Local_Same ((cs.filter (fun c => (ψ c).isSome)).map g₁)
      ((cs.filterMap ψ).map g₂) := by
    clear h1 h2 hperm hv'
    induction cs with
    | nil => simp
    | cons c cs ih =>
      have ih' := ih (fun c' hc' => hψ c' (List.mem_cons_of_mem _ hc'))
        (fun c' hc' => hv c' (List.mem_cons_of_mem _ hc'))
      rcases hψc : ψ c with _ | c'
      · simp only [List.filter_cons, hψc, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          List.filterMap_cons]
        exact ih'
      · simp only [List.filter_cons, hψc, Option.isSome_some, ↓reduceIte, List.filterMap_cons,
          List.map_cons]
        exact List.Forall₂.cons ((hψ c List.mem_cons_self).2 c' hψc) ih'
  exact Local_carry_trans_id h1 (Local_carry_trans_id h2 (Local_ELG_same hf2 hpin (fun e he => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
    exact hv c (List.mem_filter.1 hc).1) hvp))

end ELG

/-! ## The block reading of an atomic graph -/

section Reading

variable {k n : ℕ}

/-- The first element of `List.finRange m` satisfying `p` is the least one. -/
private theorem Local_find_least {m : ℕ} {p : Fin m → Bool} {b : Fin m}
    (h : (List.finRange m).find? p = some b) : p b = true ∧ ∀ c : Fin m, p c = true → b ≤ c := by
  obtain ⟨hb, i, hi, hib, hlt⟩ := List.find?_eq_some_iff_getElem.1 h
  refine ⟨hb, fun c hc => ?_⟩
  have hbi : (b : ℕ) = i := by
    rw [← hib, List.getElem_finRange]
    rfl
  by_contra hcb
  push Not at hcb
  have hcl : (c : ℕ) < i := by rw [← hbi]; exact hcb
  have := hlt c hcl
  have e : (List.finRange m)[(c : ℕ)]'(by simp) = c := by
    apply Fin.ext
    simp
  rw [e, hc] at this
  simp at this

/-- `List.find?` on `List.finRange m` finds an element when one satisfies the predicate. -/
private theorem Local_find_some {m : ℕ} {p : Fin m → Bool} {c : Fin m} (hc : p c = true) :
    ∃ b, (List.finRange m).find? p = some b := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨c, List.mem_finRange c, hc⟩)
  exact ⟨b, hb⟩

/-- The reading of an atom: the molecule of its atom in the block normal form. -/
private def Local_rho (Γ : Graph k n) (u : Atom k n) : Atom k n := Γ.molRep (Γ.flatAtom u)

/-- The entry of a component in the block reading of `Γ`. -/
private def Local_rd (Γ : Graph k n) (c : Comp (Atom k n)) : Local_Ed (Atom k n) :=
  (if c.kind = .dot ∨ Local_rho Γ c.x = Local_rho Γ c.y then none else c.kind.mclass,
    Local_rho Γ c.x, Local_rho Γ c.y)

/-- The pin edge at the external atom `a` in the block reading of `Γ`. -/
private def Local_pin (Γ : Graph k n) (a : Fin k) : Local_Ed (Atom k n) :=
  match Γ.anchor (.inl a) with
  | some b => (some (pinClass a), Γ.molRep (.inr b), .inl a)
  | none => (none, .inl a, .inl a)

/-- The graph of a list of components read in `Γ`. -/
private def Local_RG (Γ : Graph k n) (L : List (Comp (Atom k n))) :
    MGraph (Atom k n) (Fin (L.map (Local_rd Γ)).length ⊕ Fin k) :=
  Local_ELG Γ.toMG'.int Γ.toMG'.ext (Local_pin Γ) (L.map (Local_rd Γ))

private theorem Local_anchor_some {Γ : Graph k n} {u : Atom k n} {b : Fin n}
    (h : Γ.anchor u = some b) : Γ.SameBlock u (.inr b) := by
  unfold Graph.anchor at h
  have hb := List.find?_some h
  exact of_decide_eq_true hb

private theorem Local_anchor_none {Γ : Graph k n} {u : Atom k n} :
    Γ.anchor u = none ↔ ∀ b, ¬ Γ.SameBlock u (.inr b) := by
  unfold Graph.anchor
  rw [List.find?_eq_none]
  simp

/-- The anchor is the least internal atom of the block. -/
private theorem Local_anchor_least {Γ : Graph k n} {u : Atom k n} {b : Fin n}
    (h : Γ.anchor u = some b) : Γ.SameBlock u (.inr b) ∧ ∀ c, Γ.SameBlock u (.inr c) → b ≤ c := by
  unfold Graph.anchor at h
  obtain ⟨h1, h2⟩ := Local_find_least h
  exact ⟨of_decide_eq_true h1, fun c hc => h2 c (decide_eq_true hc)⟩

private theorem Local_anchor_of_least {Γ : Graph k n} {u : Atom k n} {b : Fin n}
    (h1 : Γ.SameBlock u (.inr b)) (h2 : ∀ c, Γ.SameBlock u (.inr c) → b ≤ c) :
    Γ.anchor u = some b := by
  rcases hA : Γ.anchor u with _ | b'
  · exact absurd h1 (Local_anchor_none.1 hA b)
  · obtain ⟨h1', h2'⟩ := Local_anchor_least hA
    exact congrArg some (le_antisymm (h2' b h1) (h2 b' h1'))

private theorem Local_flat_block (Γ : Graph k n) (u : Atom k n) :
    Γ.SameBlock u (Γ.flatAtom u) := by
  cases u with
  | inr b => exact SimpleGraph.Reachable.refl _
  | inl a =>
    rcases hA : Γ.anchor (.inl a) with _ | b
    · simp only [Graph.flatAtom, hA]
      exact SimpleGraph.Reachable.refl _
    · simp only [Graph.flatAtom, hA]
      exact Local_anchor_some hA

private theorem Local_flat_isRight {Γ : Graph k n} {u : Atom k n} (h : ¬ Γ.Unpinned u) :
    (Γ.flatAtom u).isRight = true := by
  cases u with
  | inr b => rfl
  | inl a =>
    rcases hA : Γ.anchor (.inl a) with _ | b
    · exact absurd ⟨rfl, Local_anchor_none.1 hA⟩ h
    · simp only [Graph.flatAtom, hA]
      rfl

private theorem Local_flat_unpinned {Γ : Graph k n} {u : Atom k n} (h : Γ.Unpinned u) :
    Γ.flatAtom u = u := by
  obtain ⟨-, h2⟩ := h
  cases u with
  | inr b => rfl
  | inl a =>
    have hA : Γ.anchor (.inl a) = none := Local_anchor_none.2 h2
    simp only [Graph.flatAtom, hA]

private theorem Local_dot_le_mol (Γ : Graph k n) : Γ.dotGraph ≤ Γ.molGraph := by
  intro u v huv
  simp only [Graph.dotGraph, Graph.molGraph, SimpleGraph.fromRel_adj] at huv ⊢
  refine ⟨huv.1, ?_⟩
  rcases huv.2 with ⟨c, hc, hk, h1, h2⟩ | ⟨c, hc, hk, h1, h2⟩
  · exact Or.inl ⟨c, hc, by simp [hk, Kind.joinsMol], h1, h2⟩
  · exact Or.inr ⟨c, hc, by simp [hk, Kind.joinsMol], h1, h2⟩

/-- The representative of an internal atom is the least internal atom of its molecule. -/
private theorem Local_molRep_least (Γ : Graph k n) (a : Fin n) :
    ∃ b, Γ.molRep (.inr a) = .inr b ∧ Γ.SameMol (.inr a) (.inr b) ∧
      ∀ c, Γ.SameMol (.inr a) (.inr c) → b ≤ c := by
  obtain ⟨b, hb⟩ := Local_find_some (p := fun b : Fin n => decide (Γ.SameMol (.inr a) (.inr b)))
    (c := a) (decide_eq_true (Or.inl rfl))
  obtain ⟨h1, h2⟩ := Local_find_least hb
  refine ⟨b, by simp [Graph.molRep, hb], of_decide_eq_true h1, fun c hc => h2 c (decide_eq_true hc)⟩

private theorem Local_molRep_spec (Γ : Graph k n) (u : Atom k n) :
    Γ.SameMol u (Γ.molRep u) := by
  cases u with
  | inl a => exact Or.inl rfl
  | inr a =>
    obtain ⟨b, hb, h, -⟩ := Local_molRep_least Γ a
    rw [hb]
    exact h

private theorem Local_molRep_eq_iff (Γ : Graph k n) (u v : Atom k n) :
    Γ.molRep u = Γ.molRep v ↔ Γ.SameMol u v := by
  have E := Γ.sameMol_equivalence
  constructor
  · intro h
    exact E.trans (Local_molRep_spec Γ u) (h ▸ E.symm (Local_molRep_spec Γ v))
  · intro h
    cases u with
    | inl a =>
      rcases h with rfl | ⟨h1, -⟩
      · rfl
      · exact absurd h1 (by simp)
    | inr a =>
      cases v with
      | inl b =>
        rcases h with h | ⟨-, h2, -⟩
        · exact absurd h (by simp)
        · exact absurd h2 (by simp)
      | inr b =>
        obtain ⟨c, hc, hac, hcl⟩ := Local_molRep_least Γ a
        obtain ⟨d, hd, hbd, hdl⟩ := Local_molRep_least Γ b
        rw [hc, hd]
        congr 1
        exact le_antisymm (hcl d (E.trans h hbd)) (hdl c (E.trans (E.symm h) hac))

private theorem Local_molRep_idem (Γ : Graph k n) (v : Atom k n) :
    Γ.molRep (Γ.molRep v) = Γ.molRep v :=
  (Local_molRep_eq_iff _ _ _).2 (Γ.sameMol_equivalence.symm (Local_molRep_spec Γ v))

private theorem Local_molRep_flat {Γ : Graph k n} {u : Atom k n} {c : Fin n}
    (h : Γ.SameBlock u (.inr c)) : Γ.molRep (Γ.flatAtom u) = Γ.molRep (.inr c) := by
  have hr := Local_flat_isRight (u := u) (Γ := Γ) (fun h' => h'.2 c h)
  have hb : Γ.SameBlock (Γ.flatAtom u) (.inr c) := (Local_flat_block Γ u).symm.trans h
  exact (Local_molRep_eq_iff Γ _ _).2
    (Or.inr ⟨hr, rfl, SimpleGraph.Reachable.mono (Local_dot_le_mol Γ) hb⟩)

private theorem Local_mem_int {Γ : Graph k n} {v : Atom k n} :
    v ∈ Γ.toMG'.int ↔ ∃ a, Γ.molRep (.inr a) = v := by
  simp [Graph.toMG']

private theorem Local_mem_ext {Γ : Graph k n} {v : Atom k n} :
    v ∈ Γ.toMG'.ext ↔ v.isLeft = true := by
  cases v <;> simp [Graph.toMG']

private theorem Local_molRep_vtx (Γ : Graph k n) (u : Atom k n) :
    Γ.toMG'.IsVtx (Γ.molRep u) := by
  cases u with
  | inl a => exact Or.inr (Local_mem_ext.2 rfl)
  | inr a => exact Or.inl (Local_mem_int.2 ⟨a, rfl⟩)

private theorem Local_rho_vtx (Γ : Graph k n) (u : Atom k n) : Γ.toMG'.IsVtx (Local_rho Γ u) :=
  Local_molRep_vtx Γ _

private theorem Local_pin_vok (Γ : Graph k n) (a : Fin k) :
    Local_VOK Γ.toMG'.int Γ.toMG'.ext (Local_pin Γ a) := by
  intro h
  unfold Local_pin at h ⊢
  rcases hA : Γ.anchor (.inl a) with _ | b <;> simp only [hA] at h ⊢
  · exact absurd rfl h
  · exact ⟨Local_molRep_vtx Γ _, Or.inr (Local_mem_ext.2 rfl)⟩

private theorem Local_rd_vok (Γ : Graph k n) (c : Comp (Atom k n)) :
    Local_VOK Γ.toMG'.int Γ.toMG'.ext (Local_rd Γ c) :=
  fun _ => ⟨Local_rho_vtx Γ _, Local_rho_vtx Γ _⟩

/-- `Graph.toMG'` and the graph of the components read in the graph agree up to the positions. -/
private theorem Local_toMG'_cls (Γ : Graph k n) (i : Fin Γ.comps.length) :
    Γ.toMG'.cls (.inl i) = (Local_rd Γ Γ.comps[i]).1 ∧
      (Γ.toMG'.cls (.inl i) ≠ none → Γ.toMG'.ends (.inl i) = (Local_rd Γ Γ.comps[i]).2) := by
  by_cases hk : Γ.comps[i.val].kind = .dot
  · refine ⟨by simp [Graph.toMG', Graph.flatComp, hk, Local_rd], fun h => absurd ?_ h⟩
    simp [Graph.toMG', Graph.flatComp, hk]
  · refine ⟨?_, fun _ => ?_⟩
    · simp [Graph.toMG', Graph.flatComp, hk, Local_rd, Local_rho]
    · simp [Graph.toMG', Graph.flatComp, hk, Local_rd, Local_rho]

private theorem Local_toMG'_pin (Γ : Graph k n) (a : Fin k) :
    Γ.toMG'.cls (.inr a) = (Local_pin Γ a).1 ∧ Γ.toMG'.ends (.inr a) = (Local_pin Γ a).2 := by
  unfold Local_pin
  simp only [Graph.toMG']
  split <;> simp_all

/-- `Graph.toMG'` is carried by the identity to the graph of its components read in the graph. -/
private theorem Local_carry_toRG {k n : ℕ} (Γ : Graph k n) :
    Local_Carry Γ.toMG' (Local_RG Γ Γ.comps) id := by
  refine Local_carry_cast (List.length_map _).symm _ _ rfl rfl (fun i => ?_) (fun a => ?_)
    (fun i hne => ?_) (fun a _ => ?_) (fun e he => ?_)
  · change (Γ.comps.map (Local_rd Γ))[(i : ℕ)].1 = _
    rw [List.getElem_map, (Local_toMG'_cls Γ i).1]
    rfl
  · exact (Local_toMG'_pin Γ a).1.symm
  · change (Γ.comps.map (Local_rd Γ))[(i : ℕ)].2 = _
    rw [List.getElem_map, (Local_toMG'_cls Γ i).2 hne]
    rfl
  · exact (Local_toMG'_pin Γ a).2.symm
  · rcases e with i | a
    · rw [(Local_toMG'_cls Γ i).1] at he
      rw [(Local_toMG'_cls Γ i).2 (by rw [(Local_toMG'_cls Γ i).1]; exact he)]
      exact Local_rd_vok Γ _ he
    · rw [(Local_toMG'_pin Γ a).1] at he
      rw [(Local_toMG'_pin Γ a).2]
      exact Local_pin_vok Γ a he

/-- The graph of the components read in the graph is carried by the identity to `Graph.toMG'`. -/
private theorem Local_carry_ofRG {k n : ℕ} (Γ : Graph k n) :
    Local_Carry (Local_RG Γ Γ.comps) Γ.toMG' id := by
  refine Local_carry_cast (List.length_map _) _ _ rfl rfl (fun i => ?_) (fun a => ?_)
    (fun i hne => ?_) (fun a _ => ?_) (fun e he => ?_)
  · change _ = (Γ.comps.map (Local_rd Γ))[(i : ℕ)].1
    rw [List.getElem_map, (Local_toMG'_cls Γ (Fin.cast (List.length_map _) i)).1]
    rfl
  · exact (Local_toMG'_pin Γ a).1
  · change (Γ.comps.map (Local_rd Γ))[(i : ℕ)].1 ≠ none at hne
    rw [List.getElem_map] at hne
    change _ = (Γ.comps.map (Local_rd Γ))[(i : ℕ)].2
    rw [List.getElem_map, (Local_toMG'_cls Γ (Fin.cast (List.length_map _) i)).2 (by
      rw [(Local_toMG'_cls Γ _).1]; exact hne)]
    rfl
  · exact (Local_toMG'_pin Γ a).2
  · rcases e with i | a
    · exact Local_ELG_vok_inl (Γ.comps.map (Local_rd Γ)) (fun e he' => by
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 he'
        exact Local_rd_vok Γ c) i he
    · exact Local_pin_vok Γ a he

end Reading

/-! ## Graphs with new internal atoms joined to the molecule of `x` -/

section Lift

variable {k n : ℕ}

/-- The atom of the input graph read for an atom of a graph with `j` more internal atoms: old
atoms keep their indices and the new atoms are read at `x`. -/
private def Local_proj (j : ℕ) (x : Fin n) : Atom k (n + j) → Atom k n
  | .inl a => .inl a
  | .inr i => if h : (i : ℕ) < n then .inr ⟨i, h⟩ else .inr x

private theorem Local_proj_lift (j : ℕ) (x : Fin n) (u : Atom k n) :
    Local_proj j x (liftA j u) = u := by
  cases u <;> simp [Local_proj, liftA]

private theorem Local_proj_new {j : ℕ} (x : Fin n) (i : Fin j) :
    Local_proj (k := k) j x (newA i) = .inr x := by
  simp [Local_proj, newA]

private theorem Local_lift_inj (j : ℕ) : Function.Injective (liftA (k := k) (n := n) j) := by
  rintro (a | a) (b | b) h <;> simp_all [liftA, Fin.ext_iff]

private theorem Local_lift_ne_new (j : ℕ) (u : Atom k n) (i : Fin j) : liftA j u ≠ newA i := by
  cases u with
  | inl a => simp [liftA, newA]
  | inr a =>
    simp only [liftA, newA, Sum.map_inr, ne_eq, Sum.inr.injEq, Fin.ext_iff, Fin.coe_castAdd,
      Fin.coe_natAdd]
    omega

private theorem Local_atom_cases (j : ℕ) (u : Atom k (n + j)) :
    (∃ v, u = liftA j v) ∨ ∃ i : Fin j, u = newA i := by
  rcases u with a | i
  · exact Or.inl ⟨.inl a, rfl⟩
  · by_cases h : (i : ℕ) < n
    · exact Or.inl ⟨.inr ⟨i, h⟩, by simp [liftA, Fin.ext_iff]⟩
    · exact Or.inr ⟨⟨i - n, by omega⟩, by simp [newA, Fin.ext_iff]; omega⟩

private theorem Local_lift_isRight (j : ℕ) (u : Atom k n) : (liftA j u).isRight = u.isRight := by
  cases u <;> rfl

private theorem Local_comp_proj_lift (j : ℕ) (x : Fin n) (c : Comp (Atom k n)) :
    (c.map (liftA j)).map (Local_proj j x) = c := by
  obtain ⟨κ, a, b, m, l⟩ := c
  simp only [Comp.map, Local_proj_lift, List.map_map]
  congr 1
  · conv_rhs => rw [← List.map_id m]
    exact List.map_congr_left (fun u _ => Local_proj_lift j x u)
  · cases l with
    | none => rfl
    | some p =>
      obtain ⟨q, u⟩ := p
      simp [Prod.map, Local_proj_lift]

/-- Reachability is carried by a map that sends adjacent vertices to reachable ones. -/
private theorem Local_reach_map {W W' : Type} {G : SimpleGraph W} {G' : SimpleGraph W'}
    (f : W → W') (h : ∀ a b, G.Adj a b → G'.Reachable (f a) (f b)) {u v : W}
    (huv : G.Reachable u v) : G'.Reachable (f u) (f v) := by
  obtain ⟨w⟩ := huv
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons ha _ ih => exact (h _ _ ha).trans ih

/-- The conditions on a graph `Γ'` with `j` more internal atoms than `Γ`: the same dotted edges;
the waved and dotted edges of `Γ`, and besides them only waved and dotted edges with both ends read
in the molecule of `x`; every new atom joined to `x`. -/
private structure Local_LiftOK (Γ : Graph k n) (x : Fin n) (j : ℕ) (Γ' : Graph k (n + j)) :
    Prop where
  d1 : ∀ c ∈ Γ.comps, c.kind = .dot → ∃ c' ∈ Γ'.comps, c'.kind = .dot ∧ c'.x = liftA j c.x ∧
    c'.y = liftA j c.y
  d2 : ∀ c' ∈ Γ'.comps, c'.kind = .dot → ∃ c ∈ Γ.comps, c.kind = .dot ∧ c'.x = liftA j c.x ∧
    c'.y = liftA j c.y
  m1 : ∀ c ∈ Γ.comps, c.kind.joinsMol = true → ∃ c' ∈ Γ'.comps, c'.kind.joinsMol = true ∧
    c'.x = liftA j c.x ∧ c'.y = liftA j c.y
  m2 : ∀ c' ∈ Γ'.comps, c'.kind.joinsMol = true →
    (∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c'.x = liftA j c.x ∧ c'.y = liftA j c.y) ∨
      (Γ.SameMol (Local_proj j x c'.x) (.inr x) ∧ Γ.SameMol (Local_proj j x c'.y) (.inr x))
  m3 : ∀ i : Fin j, Γ'.molGraph.Reachable (newA i) (liftA j (.inr x))

section LiftOK

variable {Γ : Graph k n} {x : Fin n} {j : ℕ} {Γ' : Graph k (n + j)}

private theorem Local_lift_sameBlock (h : Local_LiftOK Γ x j Γ') (u v : Atom k n) :
    Γ'.SameBlock (liftA j u) (liftA j v) ↔ Γ.SameBlock u v := by
  constructor
  · intro hr
    have := Local_reach_map (G := Γ'.dotGraph) (G' := Γ.dotGraph) (Local_proj j x) (fun a b hab => ?_)
      hr
    · rw [Local_proj_lift, Local_proj_lift] at this
      exact this
    · simp only [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab
      obtain ⟨hne, hab⟩ := hab
      have key : ∀ a b, (∃ c ∈ Γ'.comps, c.kind = .dot ∧ c.x = a ∧ c.y = b) →
          Γ.dotGraph.Reachable (Local_proj j x a) (Local_proj j x b) := by
        rintro a b ⟨c', hc', hk, rfl, rfl⟩
        obtain ⟨c, hc, hk', h1, h2⟩ := h.d2 c' hc' hk
        rw [h1, h2, Local_proj_lift, Local_proj_lift]
        by_cases hxy : c.x = c.y
        · rw [hxy]
        · exact SimpleGraph.Adj.reachable (by
            simp only [Graph.dotGraph, SimpleGraph.fromRel_adj]
            exact ⟨hxy, Or.inl ⟨c, hc, hk', rfl, rfl⟩⟩)
      rcases hab with hab | hab
      · exact key a b hab
      · exact (key b a hab).symm
  · intro hr
    refine Local_reach_map (liftA j) (fun a b hab => ?_) hr
    simp only [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab
    obtain ⟨hne, hab⟩ := hab
    have key : ∀ a b, (∃ c ∈ Γ.comps, c.kind = .dot ∧ c.x = a ∧ c.y = b) → a ≠ b →
        Γ'.dotGraph.Reachable (liftA j a) (liftA j b) := by
      rintro a b ⟨c, hc, hk, rfl, rfl⟩ hne
      obtain ⟨c', hc', hk', h1, h2⟩ := h.d1 c hc hk
      exact SimpleGraph.Adj.reachable (by
        simp only [Graph.dotGraph, SimpleGraph.fromRel_adj]
        exact ⟨fun e => hne (Local_lift_inj j e), Or.inl ⟨c', hc', hk', h1, h2⟩⟩)
    rcases hab with hab | hab
    · exact key a b hab hne
    · exact (key b a hab (Ne.symm hne)).symm

/-- A new atom is alone in its block. -/
private theorem Local_new_block (h : Local_LiftOK Γ x j Γ') (i : Fin j) {v : Atom k (n + j)}
    (hv : Γ'.SameBlock (newA i) v) : v = newA i := by
  obtain ⟨w⟩ := hv
  cases w with
  | nil => rfl
  | cons ha _ =>
    exfalso
    simp only [Graph.dotGraph, SimpleGraph.fromRel_adj] at ha
    rcases ha.2 with ⟨c', hc', hk, h1, -⟩ | ⟨c', hc', hk, -, h2⟩
    · obtain ⟨c, -, -, h1', -⟩ := h.d2 c' hc' hk
      exact Local_lift_ne_new j c.x i (h1'.symm.trans h1)
    · obtain ⟨c, -, -, -, h2'⟩ := h.d2 c' hc' hk
      exact Local_lift_ne_new j c.y i (h2'.symm.trans h2)

private theorem Local_lift_anchor (h : Local_LiftOK Γ x j Γ') (u : Atom k n) :
    Γ'.anchor (liftA j u) = (Γ.anchor u).map (Fin.castAdd j) := by
  rcases hA : Γ.anchor u with _ | b
  · simp only [Option.map_none]
    rw [Local_anchor_none]
    intro b' hb'
    rcases Local_atom_cases j (.inr b') with ⟨v, hv⟩ | ⟨i, hi⟩
    · obtain ⟨b, rfl⟩ : ∃ b, v = .inr b := by
        cases v with
        | inl a => simp [liftA] at hv
        | inr b => exact ⟨b, rfl⟩
      rw [hv, Local_lift_sameBlock h] at hb'
      exact Local_anchor_none.1 hA b hb'
    · rw [hi] at hb'
      exact Local_lift_ne_new j u i (Local_new_block h i hb'.symm)
  · obtain ⟨h1, h2⟩ := Local_anchor_least hA
    simp only [Option.map_some]
    refine Local_anchor_of_least ?_ fun c hc => ?_
    · exact (Local_lift_sameBlock h u (.inr b)).2 h1
    · rcases Local_atom_cases j (.inr c) with ⟨v, hv⟩ | ⟨i, hi⟩
      · obtain ⟨b', rfl⟩ : ∃ b', v = .inr b' := by
          cases v with
          | inl a => simp [liftA] at hv
          | inr b' => exact ⟨b', rfl⟩
        have hcb : c = Fin.castAdd j b' := by simpa [liftA] using hv
        rw [hv, Local_lift_sameBlock h] at hc
        rw [hcb]
        exact Fin.le_def.2 (by simpa using Fin.le_def.1 (h2 b' hc))
      · rw [hi] at hc
        exact absurd (Local_new_block h i hc.symm) (Local_lift_ne_new j u i)

private theorem Local_lift_flat (h : Local_LiftOK Γ x j Γ') (u : Atom k n) :
    Γ'.flatAtom (liftA j u) = liftA j (Γ.flatAtom u) := by
  cases u with
  | inr b => rfl
  | inl a =>
    have hA := Local_lift_anchor h (.inl a)
    change Γ'.anchor (.inl a) = _ at hA
    show Γ'.flatAtom (.inl a) = liftA j (Γ.flatAtom (.inl a))
    unfold Graph.flatAtom
    rw [hA]
    rcases Γ.anchor (.inl a) with _ | b <;> rfl

private theorem Local_lift_unpinned (h : Local_LiftOK Γ x j Γ') (u : Atom k n) :
    Γ'.Unpinned (liftA j u) ↔ Γ.Unpinned u := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by cases u <;> simp_all [liftA], fun b hb => ?_⟩
    exact h2 (Fin.castAdd j b) ((Local_lift_sameBlock h u (.inr b)).2 hb)
  · rintro ⟨h1, h2⟩
    refine ⟨by cases u <;> simp_all [liftA], fun b' hb' => ?_⟩
    rcases Local_atom_cases j (.inr b') with ⟨v, hv⟩ | ⟨i, hi⟩
    · obtain ⟨b, rfl⟩ : ∃ b, v = .inr b := by
        cases v with
        | inl a => simp [liftA] at hv
        | inr b => exact ⟨b, rfl⟩
      rw [hv, Local_lift_sameBlock h] at hb'
      exact h2 b hb'
    · rw [hi] at hb'
      exact Local_lift_ne_new j u i (Local_new_block h i hb'.symm)

/-- The molecules of `Γ'` read through `Local_proj`. -/
private theorem Local_lift_molReach (h : Local_LiftOK Γ x j Γ') {a b : Atom k (n + j)}
    (hr : Γ'.molGraph.Reachable a b) :
    Γ.molGraph.Reachable (Local_proj j x a) (Local_proj j x b) := by
  have hx : ∀ u, Γ.SameMol u (.inr x) → Γ.molGraph.Reachable u (.inr x) := by
    rintro u (rfl | ⟨-, -, hr⟩)
    · exact SimpleGraph.Reachable.refl _
    · exact hr
  refine Local_reach_map (Local_proj j x) (fun a b hab => ?_) hr
  simp only [Graph.molGraph, SimpleGraph.fromRel_adj] at hab
  obtain ⟨hne, hab⟩ := hab
  have key : ∀ a b, (∃ c ∈ Γ'.comps, c.kind.joinsMol = true ∧ c.x = a ∧ c.y = b) →
      Γ.molGraph.Reachable (Local_proj j x a) (Local_proj j x b) := by
    rintro a b ⟨c', hc', hk, rfl, rfl⟩
    rcases h.m2 c' hc' hk with ⟨c, hc, hk', h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, Local_proj_lift, Local_proj_lift]
      by_cases hxy : c.x = c.y
      · rw [hxy]
      · exact SimpleGraph.Adj.reachable (by
          simp only [Graph.molGraph, SimpleGraph.fromRel_adj]
          exact ⟨hxy, Or.inl ⟨c, hc, hk', rfl, rfl⟩⟩)
    · exact (hx _ h1).trans (hx _ h2).symm
  rcases hab with hab | hab
  · exact key a b hab
  · exact (key b a hab).symm

private theorem Local_lift_molReach' (h : Local_LiftOK Γ x j Γ') {u v : Atom k n}
    (hr : Γ.molGraph.Reachable u v) : Γ'.molGraph.Reachable (liftA j u) (liftA j v) := by
  refine Local_reach_map (liftA j) (fun a b hab => ?_) hr
  simp only [Graph.molGraph, SimpleGraph.fromRel_adj] at hab
  obtain ⟨hne, hab⟩ := hab
  have key : ∀ a b, (∃ c ∈ Γ.comps, c.kind.joinsMol = true ∧ c.x = a ∧ c.y = b) → a ≠ b →
      Γ'.molGraph.Reachable (liftA j a) (liftA j b) := by
    rintro a b ⟨c, hc, hk, rfl, rfl⟩ hne
    obtain ⟨c', hc', hk', h1, h2⟩ := h.m1 c hc hk
    exact SimpleGraph.Adj.reachable (by
      simp only [Graph.molGraph, SimpleGraph.fromRel_adj]
      exact ⟨fun e => hne (Local_lift_inj j e), Or.inl ⟨c', hc', hk', h1, h2⟩⟩)
  rcases hab with hab | hab
  · exact key a b hab hne
  · exact (key b a hab (Ne.symm hne)).symm

/-- Every internal atom of `Γ'` is joined to the original atom of its reading. -/
private theorem Local_lift_toProj (h : Local_LiftOK Γ x j Γ') (a : Atom k (n + j)) :
    Γ'.molGraph.Reachable a (liftA j (Local_proj j x a)) := by
  rcases Local_atom_cases j a with ⟨v, rfl⟩ | ⟨i, rfl⟩
  · rw [Local_proj_lift]
  · rw [Local_proj_new]
    exact h.m3 i

private theorem Local_proj_isRight (j : ℕ) (x : Fin n) (a : Atom k (n + j)) :
    (Local_proj j x a).isRight = a.isRight := by
  rcases a with a | i
  · rfl
  · simp only [Local_proj]
    split_ifs <;> rfl

private theorem Local_lift_sameMol (h : Local_LiftOK Γ x j Γ') (a b : Atom k (n + j)) :
    Γ'.SameMol a b ↔ Γ.SameMol (Local_proj j x a) (Local_proj j x b) := by
  constructor
  · rintro (rfl | ⟨h1, h2, hr⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨by rwa [Local_proj_isRight], by rwa [Local_proj_isRight],
        Local_lift_molReach h hr⟩
  · rintro (he | ⟨h1, h2, hr⟩)
    · rcases a with a | a <;> rcases b with b | b
      · simp only [Local_proj, Sum.inl.injEq] at he
        exact Or.inl (by rw [he])
      · simp only [Local_proj] at he
        split_ifs at he
      · simp only [Local_proj] at he
        split_ifs at he
      · refine Or.inr ⟨rfl, rfl, ?_⟩
        have h1' := Local_lift_toProj h (.inr a)
        rw [he] at h1'
        exact h1'.trans (Local_lift_toProj h (.inr b)).symm
    · refine Or.inr ⟨by rwa [Local_proj_isRight] at h1, by rwa [Local_proj_isRight] at h2, ?_⟩
      exact ((Local_lift_toProj h a).trans (Local_lift_molReach' h hr)).trans
        (Local_lift_toProj h b).symm

private theorem Local_lift_molRep (h : Local_LiftOK Γ x j Γ') (a : Atom k (n + j)) :
    Γ'.molRep a = liftA j (Γ.molRep (Local_proj j x a)) := by
  rcases a with a | i
  · rfl
  · obtain ⟨b', hb', hs', hl'⟩ := Local_molRep_least Γ' i
    obtain ⟨c, hc⟩ : ∃ c, Local_proj j x (.inr i : Atom k (n + j)) = .inr c := by
      simp only [Local_proj]
      split_ifs <;> exact ⟨_, rfl⟩
    obtain ⟨b, hb, hs, hl⟩ := Local_molRep_least Γ c
    rw [hb', hc, hb]
    have hcast : (Fin.castAdd j b : Fin (n + j)) = b' := by
      have h1 : Γ'.SameMol (.inr i) (.inr (Fin.castAdd j b)) := by
        rw [Local_lift_sameMol h, hc]
        have e := Local_proj_lift (k := k) j x (.inr b)
        simp only [liftA, Sum.map_inr] at e
        rw [e]
        exact hs
      have hle := hl' _ h1
      have hlt : (b' : ℕ) < n := lt_of_le_of_lt (Fin.le_def.1 hle) (by simp)
      have h2 : Γ.SameMol (.inr c) (.inr ⟨b', hlt⟩) := by
        have := (Local_lift_sameMol h _ _).1 hs'
        rw [hc] at this
        simpa [Local_proj, hlt] using this
      have := hl _ h2
      exact (le_antisymm hle (Fin.le_def.2 (by simpa [Fin.le_def] using this))).symm
    simp [liftA, hcast]

private theorem Local_lift_rho (h : Local_LiftOK Γ x j Γ') (a : Atom k (n + j)) :
    Local_rho Γ' a = liftA j (Local_rho Γ (Local_proj j x a)) := by
  rcases Local_atom_cases j a with ⟨v, rfl⟩ | ⟨i, rfl⟩
  · unfold Local_rho
    rw [Local_lift_flat h, Local_lift_molRep h, Local_proj_lift, Local_proj_lift]
  · unfold Local_rho
    have e : Γ'.flatAtom (newA i) = newA i := rfl
    rw [e, Local_lift_molRep h, Local_proj_new]
    rfl

private theorem Local_lift_pin (h : Local_LiftOK Γ x j Γ') (a : Fin k) :
    Local_pin Γ' a = ((Local_pin Γ a).1, liftA j (Local_pin Γ a).2.1,
      liftA j (Local_pin Γ a).2.2) := by
  unfold Local_pin
  have hA := Local_lift_anchor h (.inl a)
  change Γ'.anchor (.inl a) = _ at hA
  rw [hA]
  rcases Γ.anchor (.inl a) with _ | b
  · rfl
  · simp only [Option.map_some]
    rw [Local_lift_molRep h]
    simp [Local_proj, liftA]

private theorem Local_lift_int (h : Local_LiftOK Γ x j Γ') :
    Γ'.toMG'.int = Γ.toMG'.int.image (liftA j) := by
  ext v
  simp only [Local_mem_int, Finset.mem_image]
  constructor
  · rintro ⟨a, rfl⟩
    rw [Local_lift_molRep h]
    obtain ⟨c, hc⟩ : ∃ c, Local_proj j x (.inr a : Atom k (n + j)) = .inr c := by
      simp only [Local_proj]
      split_ifs <;> exact ⟨_, rfl⟩
    exact ⟨_, ⟨c, by rw [hc]⟩, rfl⟩
  · rintro ⟨w, ⟨a, rfl⟩, rfl⟩
    refine ⟨Fin.castAdd j a, ?_⟩
    rw [Local_lift_molRep h]
    simp [Local_proj, liftA]

private theorem Local_lift_ext (j : ℕ) {Γ : Graph k n} {Γ' : Graph k (n + j)} :
    Γ'.toMG'.ext = Γ.toMG'.ext.image (liftA j) := by
  ext v
  simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨.inl a, ⟨a, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩

private theorem Local_lift_rd (h : Local_LiftOK Γ x j Γ') (c : Comp (Atom k (n + j))) :
    Local_rd Γ' c = ((Local_rd Γ (c.map (Local_proj j x))).1,
      liftA j (Local_rd Γ (c.map (Local_proj j x))).2.1,
      liftA j (Local_rd Γ (c.map (Local_proj j x))).2.2) := by
  unfold Local_rd
  rw [Local_lift_rho h, Local_lift_rho h]
  refine Prod.ext ?_ rfl
  dsimp only
  split_ifs with h1 h2 h2
  · rfl
  · exfalso
    apply h2
    simp only [Comp.map]
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Local_lift_inj j h1)
  · exfalso
    apply h1
    simp only [Comp.map] at h2
    rcases h2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (by rw [h2])
  · rfl

/-- The graph `Γ'` with new internal atoms joined to the molecule of `x` is carried from its
components read in `Γ` through `Local_proj`, along `liftA j`. -/
private theorem Local_carry_lift (h : Local_LiftOK Γ x j Γ') :
    Local_Carry (Local_RG Γ (Γ'.comps.map (Comp.map (Local_proj j x)))) Γ'.toMG' (liftA j) := by
  have hlen : ((Γ'.comps.map (Comp.map (Local_proj j x))).map (Local_rd Γ)).length =
      Γ'.comps.length := by simp
  refine Local_carry_tr (g := Sum.map (Fin.cast hlen) id) ⟨?_, (Local_lift_inj j).injOn,
    Local_lift_int h, Local_lift_ext j (Γ := Γ), ?_, ?_, ?_, ?_⟩
  · rintro (i | a) (i' | a') _ _ hh
    · simp only [Sum.map_inl, Sum.inl.injEq] at hh
      exact congrArg Sum.inl (Fin.cast_injective hlen hh)
    · simp at hh
    · simp at hh
    · simpa using hh
  · rintro (i | a) he
    · exact Local_ELG_vok_inl _ (fun e he' => by
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 he'
        exact Local_rd_vok Γ c) i he
    · exact Local_pin_vok Γ a he
  · rintro (i | a) _
    · simp only [Sum.map_inl]
      rw [(Local_toMG'_cls Γ' _).1, Local_lift_rd h]
      simp [Local_RG, Local_ELG]
    · simp only [Sum.map_inr, id]
      rw [(Local_toMG'_pin Γ' a).1, Local_lift_pin h]
      rfl
  · rintro (i | a) he
    · left
      simp only [Sum.map_inl]
      rw [(Local_toMG'_cls Γ' _).2 (by
        rw [(Local_toMG'_cls Γ' _).1, Local_lift_rd h]
        simpa [Local_RG, Local_ELG] using he), Local_lift_rd h]
      simp [Local_RG, Local_ELG]
    · left
      simp only [Sum.map_inr, id]
      rw [(Local_toMG'_pin Γ' a).2, Local_lift_pin h]
      rfl
  · rintro (i | a) hh
    · have := hh (.inl (Fin.cast hlen.symm i))
      simp only [Sum.map_inl, Fin.cast_cast, Fin.cast_eq_self, ne_eq, not_true_eq_false,
        imp_false, not_not] at this
      rw [(Local_toMG'_cls Γ' _).1, Local_lift_rd h]
      simpa [Local_RG, Local_ELG] using this
    · have := hh (.inr a)
      simp only [Sum.map_inr, id, ne_eq, not_true_eq_false, imp_false, not_not] at this
      rw [(Local_toMG'_pin Γ' a).1, Local_lift_pin h]
      exact this

end LiftOK

end Lift

/-! ### Lists of components read in a graph -/

section RGOps

variable {k n : ℕ} (Γ : Graph k n)

private theorem Local_rdL_vok (L : List (Comp (Atom k n))) :
    ∀ e ∈ L.map (Local_rd Γ), Local_VOK Γ.toMG'.int Γ.toMG'.ext e := by
  intro e he
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 he
  exact Local_rd_vok Γ c

private theorem Local_RG_perm {L L' : List (Comp (Atom k n))} (h : L.Perm L') :
    Local_Carry (Local_RG Γ L) (Local_RG Γ L') id :=
  Local_ELG_perm (h.map _) (Local_rdL_vok Γ L) (Local_pin_vok Γ)

/-- Components with the same readings, one by one. -/
private def Local_SameR (c c' : Comp (Atom k n)) : Prop := Local_Same (Local_rd Γ c) (Local_rd Γ c')

private theorem Local_RG_same {L L' : List (Comp (Atom k n))}
    (h : List.Forall₂ (Local_SameR Γ) L L') : Local_Carry (Local_RG Γ L) (Local_RG Γ L') id := by
  refine Local_ELG_same ?_ (fun a => Local_Same.refl _) (Local_rdL_vok Γ L) (Local_pin_vok Γ)
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact h

private theorem Local_RG_append {L A : List (Comp (Atom k n))}
    (hA : ∀ c ∈ A, (Local_rd Γ c).1 = none) :
    Local_Carry (Local_RG Γ L) (Local_RG Γ (L ++ A)) id := by
  unfold Local_RG
  rw [List.map_append]
  exact Local_ELG_append_none (fun e he => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
    exact hA c hc) (Local_rdL_vok Γ L) (Local_pin_vok Γ)

private theorem Local_RG_drop [NeZero k] {L A : List (Comp (Atom k n))}
    (hA : ∀ c ∈ A, (Local_rd Γ c).1 = none) :
    Local_Carry (Local_RG Γ (L ++ A)) (Local_RG Γ L) id := by
  unfold Local_RG
  rw [List.map_append]
  exact Local_ELG_drop_none 0 (fun e he => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
    exact hA c hc) (Local_rdL_vok Γ L) (Local_pin_vok Γ)

private theorem Local_RG_path {L₀ : List (Comp (Atom k n))} {c p₁ p₂ : Comp (Atom k n)}
    {A B X : Atom k n} {m : MClass} (hm : m = .plus ∨ m = .minus) (hA : A ∈ Γ.toMG'.int)
    (hX : X ∈ Γ.toMG'.int) (hB : Γ.toMG'.IsVtx B)
    (hc : Local_Same (Local_rd Γ c) (Local_pe m A B)) (h₁ : Local_rd Γ p₁ = Local_pe m A X)
    (h₂ : Local_rd Γ p₂ = Local_pe m X B) :
    Local_Carry (Local_RG Γ (L₀ ++ [c])) (Local_RG Γ (L₀ ++ [p₁, p₂])) id := by
  unfold Local_RG
  rw [List.map_append, List.map_append,
    show List.map (Local_rd Γ) [p₁, p₂] = [Local_pe m A X, Local_pe m X B] by simp [h₁, h₂],
    show List.map (Local_rd Γ) [c] = [Local_rd Γ c] from rfl]
  refine Local_carry_trans_id ?_ (Local_ELG_path hm hA hX hB (Local_rdL_vok Γ L₀) (Local_pin_vok Γ))
  refine Local_ELG_same ?_ (fun a => Local_Same.refl _)
    (fun e he => ?_) (Local_pin_vok Γ)
  · exact List.rel_append (List.forall₂_same.2 (fun e _ => Local_Same.refl e))
      (List.Forall₂.cons hc List.Forall₂.nil)
  · rcases List.mem_append.1 he with he | he
    · exact Local_rdL_vok Γ L₀ e he
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      subst he
      exact Local_rd_vok Γ c

/-- The components of `Γ` up to order are `K ++ D ++ R`, those of `L'` are `K ++ D' ++ N`: the
entries of `D` and `D'` read as the same edges one by one, and those of `R` and `N` absent. -/
private theorem Local_RG_shape [NeZero k] {L' K D D' R N : List (Comp (Atom k n))}
    (hΓ : Γ.comps.Perm (K ++ D ++ R)) (hL : (K ++ D' ++ N).Perm L')
    (hDD : List.Forall₂ (Local_SameR Γ) D D') (hR : ∀ c ∈ R, (Local_rd Γ c).1 = none)
    (hN : ∀ c ∈ N, (Local_rd Γ c).1 = none) :
    Local_Carry (Local_RG Γ Γ.comps) (Local_RG Γ L') id := by
  have hKK : List.Forall₂ (Local_SameR Γ) K K :=
    List.forall₂_same.2 (fun e _ => Local_Same.refl _)
  exact Local_carry_trans_id (Local_RG_perm Γ hΓ) (Local_carry_trans_id (Local_RG_drop Γ hR)
    (Local_carry_trans_id (Local_RG_same Γ (List.rel_append hKK hDD))
      (Local_carry_trans_id (Local_RG_append Γ hN) (Local_RG_perm Γ hL))))

/-- As `Local_RG_shape`, with one more component `c` of `Γ` replaced by a path `p₁`, `p₂`. -/
private theorem Local_RG_shapeP [NeZero k] {L' K D D' R N : List (Comp (Atom k n))}
    {c p₁ p₂ : Comp (Atom k n)} {A B X : Atom k n} {m : MClass}
    (hΓ : Γ.comps.Perm (K ++ D ++ [c] ++ R)) (hL : (K ++ D' ++ [p₁, p₂] ++ N).Perm L')
    (hDD : List.Forall₂ (Local_SameR Γ) D D') (hR : ∀ c ∈ R, (Local_rd Γ c).1 = none)
    (hN : ∀ c ∈ N, (Local_rd Γ c).1 = none)
    (hm : m = .plus ∨ m = .minus) (hA : A ∈ Γ.toMG'.int)
    (hX : X ∈ Γ.toMG'.int) (hB : Γ.toMG'.IsVtx B)
    (hc : Local_Same (Local_rd Γ c) (Local_pe m A B)) (h₁ : Local_rd Γ p₁ = Local_pe m A X)
    (h₂ : Local_rd Γ p₂ = Local_pe m X B) :
    Local_Carry (Local_RG Γ Γ.comps) (Local_RG Γ L') id := by
  have hKK : List.Forall₂ (Local_SameR Γ) K K :=
    List.forall₂_same.2 (fun e _ => Local_Same.refl _)
  have hPP : List.Forall₂ (Local_SameR Γ) [p₁, p₂] [p₁, p₂] :=
    List.forall₂_same.2 (fun e _ => Local_Same.refl _)
  have p1 : (K ++ D ++ [c] ++ R).Perm (K ++ D ++ [c] ++ R) := List.Perm.refl _
  have p2 : (K ++ D ++ [p₁, p₂]).Perm (K ++ [p₁, p₂] ++ D) := by
    simp only [List.append_assoc]
    exact List.Perm.append_left K List.perm_append_comm
  have p3 : (K ++ [p₁, p₂] ++ D' ++ N).Perm (K ++ D' ++ [p₁, p₂] ++ N) := by
    simp only [List.append_assoc]
    exact List.Perm.append_left K (List.Perm.append_right N List.perm_append_comm |>
      fun h => by simpa only [List.append_assoc] using h)
  exact Local_carry_trans_id (Local_RG_perm Γ (hΓ.trans p1)) (Local_carry_trans_id
    (Local_RG_drop Γ hR) (Local_carry_trans_id (Local_RG_path Γ hm hA hX hB hc h₁ h₂)
      (Local_carry_trans_id (Local_RG_perm Γ p2) (Local_carry_trans_id
        (Local_RG_same Γ (List.rel_append (List.rel_append hKK hPP) hDD))
        (Local_carry_trans_id (Local_RG_append Γ hN) (Local_RG_perm Γ (p3.trans hL)))))))

end RGOps

/-! ## Graphs with the same kinds and ends of the components -/

section Tri

variable {k n : ℕ}

/-- The kind and the two ends of a component. -/
private def Local_tri (c : Comp (Atom k n)) : Kind × Atom k n × Atom k n := (c.kind, c.x, c.y)

/-- Two graphs whose lists of components agree in kinds and ends up to order (labels, minors and
coefficients may differ). -/
private def Local_Same3 (Γ Γ' : Graph k n) : Prop :=
  (Γ'.comps.map Local_tri).Perm (Γ.comps.map Local_tri)

private theorem Local_same3_symm {Γ Γ' : Graph k n} (h : Local_Same3 Γ Γ') : Local_Same3 Γ' Γ :=
  h.symm

private theorem Local_same3_ex {Γ Γ' : Graph k n} (h : Local_Same3 Γ Γ')
    (P : Kind → Atom k n → Atom k n → Prop) :
    (∃ c ∈ Γ'.comps, P c.kind c.x c.y) ↔ (∃ c ∈ Γ.comps, P c.kind c.x c.y) := by
  have key : ∀ {Γ Γ' : Graph k n}, (Γ'.comps.map Local_tri).Perm (Γ.comps.map Local_tri) →
      (∃ c ∈ Γ'.comps, P c.kind c.x c.y) → (∃ c ∈ Γ.comps, P c.kind c.x c.y) := by
    intro Γ Γ' h ⟨c, hc, hp⟩
    have : Local_tri c ∈ Γ.comps.map Local_tri := h.subset (List.mem_map_of_mem hc)
    obtain ⟨c', hc', he⟩ := List.mem_map.1 this
    simp only [Local_tri, Prod.mk.injEq] at he
    exact ⟨c', hc', by rw [he.1, he.2.1, he.2.2]; exact hp⟩
  exact ⟨key h, key h.symm⟩

private theorem Local_same3_all {Γ Γ' : Graph k n} (h : Local_Same3 Γ Γ')
    (P : Kind → Atom k n → Atom k n → Prop) :
    (∀ c ∈ Γ'.comps, P c.kind c.x c.y) ↔ (∀ c ∈ Γ.comps, P c.kind c.x c.y) := by
  constructor
  · intro hp
    by_contra hn
    push Not at hn
    obtain ⟨c, hc, hnp⟩ := (Local_same3_ex h (fun a b c => ¬ P a b c)).2 hn
    exact hnp (hp c hc)
  · intro hp
    by_contra hn
    push Not at hn
    obtain ⟨c, hc, hnp⟩ := (Local_same3_ex h (fun a b c => ¬ P a b c)).1 hn
    exact hnp (hp c hc)

/-- Graphs with the same dotted and molecular graphs have the same blocks, molecules and readings. -/
private theorem Local_graphs_fun {Γ Γ' : Graph k n} (hd : Γ'.dotGraph = Γ.dotGraph)
    (hm : Γ'.molGraph = Γ.molGraph) :
    Γ'.SameBlock = Γ.SameBlock ∧ Γ'.SameMol = Γ.SameMol ∧ Γ'.anchor = Γ.anchor ∧
      Γ'.molRep = Γ.molRep ∧ Γ'.flatAtom = Γ.flatAtom ∧ Γ'.Unpinned = Γ.Unpinned := by
  have hb : Γ'.SameBlock = Γ.SameBlock := by
    funext u v
    unfold Graph.SameBlock
    rw [hd]
  have hM : Γ'.SameMol = Γ.SameMol := by
    funext u v
    unfold Graph.SameMol
    rw [hm]
  have ha : Γ'.anchor = Γ.anchor := by
    funext u
    unfold Graph.anchor
    simp only [hb]
  have hr : Γ'.molRep = Γ.molRep := by
    funext u
    cases u with
    | inl a => rfl
    | inr a => simp only [Graph.molRep, hM]
  have hf : Γ'.flatAtom = Γ.flatAtom := by
    funext u
    cases u with
    | inl a => simp only [Graph.flatAtom, ha]
    | inr a => rfl
  refine ⟨hb, hM, ha, hr, hf, ?_⟩
  funext u
  unfold Graph.Unpinned
  rw [hb]

private theorem Local_same3_graphs {Γ Γ' : Graph k n} (h : Local_Same3 Γ Γ') :
    Γ'.dotGraph = Γ.dotGraph ∧ Γ'.molGraph = Γ.molGraph := by
  constructor
  · ext u v
    simp only [Graph.dotGraph, SimpleGraph.fromRel_adj]
    rw [Local_same3_ex h (fun κ a b => κ = .dot ∧ a = u ∧ b = v),
      Local_same3_ex h (fun κ a b => κ = .dot ∧ a = v ∧ b = u)]
  · ext u v
    simp only [Graph.molGraph, SimpleGraph.fromRel_adj]
    rw [Local_same3_ex h (fun κ a b => κ.joinsMol = true ∧ a = u ∧ b = v),
      Local_same3_ex h (fun κ a b => κ.joinsMol = true ∧ a = v ∧ b = u)]

private theorem Local_same3_fun {Γ Γ' : Graph k n} (h : Local_Same3 Γ Γ') :
    Γ'.SameBlock = Γ.SameBlock ∧ Γ'.SameMol = Γ.SameMol ∧ Γ'.anchor = Γ.anchor ∧
      Γ'.molRep = Γ.molRep ∧ Γ'.flatAtom = Γ.flatAtom ∧ Γ'.Unpinned = Γ.Unpinned :=
  Local_graphs_fun (Local_same3_graphs h).1 (Local_same3_graphs h).2

private theorem Local_graphs_rho {Γ Γ' : Graph k n} (hd : Γ'.dotGraph = Γ.dotGraph)
    (hm : Γ'.molGraph = Γ.molGraph) :
    Local_rho Γ' = Local_rho Γ ∧ Local_rd Γ' = Local_rd Γ ∧ Local_pin Γ' = Local_pin Γ := by
  obtain ⟨-, -, ha, hr, hf, -⟩ := Local_graphs_fun hd hm
  have hρ : Local_rho Γ' = Local_rho Γ := by
    funext u
    simp only [Local_rho, hr, hf]
  refine ⟨hρ, ?_, ?_⟩
  · funext c
    simp only [Local_rd, hρ]
  · funext a
    simp only [Local_pin, ha, hr]

private theorem Local_same3_rho {Γ Γ' : Graph k n} (h : Local_Same3 Γ Γ') :
    Local_rho Γ' = Local_rho Γ ∧ Local_rd Γ' = Local_rd Γ ∧ Local_pin Γ' = Local_pin Γ :=
  Local_graphs_rho (Local_same3_graphs h).1 (Local_same3_graphs h).2

/-- The reading of a kind and a pair of ends. -/
private def Local_rdT (Γ : Graph k n) (t : Kind × Atom k n × Atom k n) : Local_Ed (Atom k n) :=
  (if t.1 = .dot ∨ Local_rho Γ t.2.1 = Local_rho Γ t.2.2 then none else t.1.mclass,
    Local_rho Γ t.2.1, Local_rho Γ t.2.2)

private theorem Local_rd_tri (Γ : Graph k n) (c : Comp (Atom k n)) :
    Local_rd Γ c = Local_rdT Γ (Local_tri c) := rfl

private theorem Local_same3_rd {Γ Γ' : Graph k n} (h : Local_Same3 Γ Γ') :
    (Γ'.comps.map (Local_rd Γ')).Perm (Γ.comps.map (Local_rd Γ)) := by
  rw [(Local_same3_rho h).2.1]
  have e : ∀ l : List (Comp (Atom k n)), l.map (Local_rd Γ) = (l.map Local_tri).map (Local_rdT Γ) := by
    intro l
    simp [Function.comp_def, Local_rd_tri]
  rw [e, e]
  exact h.map _

/-- Graphs with the same kinds and ends of the components carry each other. -/
private theorem Local_same3_carry {Γ Γ' : Graph k n} (h : Local_Same3 Γ Γ') :
    Local_Carry Γ.toMG' Γ'.toMG' id := by
  have hr := Local_same3_rho h
  have hrd := Local_same3_rd h
  have hint : Γ'.toMG'.int = Γ.toMG'.int := by
    simp only [Graph.toMG', (Local_same3_fun h).2.2.2.1]
  have h1 := Local_carry_toRG Γ
  have h3 := Local_carry_ofRG Γ'
  refine Local_carry_trans_id h1 (Local_carry_trans_id ?_ h3)
  unfold Local_RG
  rw [hint, hr.2.2]
  exact Local_ELG_perm hrd.symm (Local_rdL_vok Γ Γ.comps) (Local_pin_vok Γ)

private theorem Local_same3_clauses {Γ Γ' : Graph 3 n} (h : Local_Same3 Γ Γ') :
    (Γ'.ColourInvB ↔ Γ.ColourInvB) ∧ (Γ'.ExtClause ↔ Γ.ExtClause) ∧ (Γ'.NoGhost ↔ Γ.NoGhost) := by
  obtain ⟨hb, -, -, -, hf, hu⟩ := Local_same3_fun h
  refine ⟨?_, ?_, ?_⟩
  · unfold Graph.ColourInvB Graph.ColourInv' Graph.blockNorm
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    simp only [Graph.flatComp, hf]
    exact Local_same3_all h (fun κ a b => ((if κ = .dot then κ else κ).isRandom = true →
      (if κ = .dot then a else Γ.flatAtom a).isRight = true ∧
      (if κ = .dot then b else Γ.flatAtom b) ≠ .inl 0 ∧
      ((if κ = .dot then b else Γ.flatAtom b) = .inl 1 → κ = .G .plus) ∧
      ((if κ = .dot then b else Γ.flatAtom b) = .inl 2 → κ = .G .minus)) ∧
      (κ = .waved .s → (if κ = .dot then a else Γ.flatAtom a).isRight = true ∧
        (if κ = .dot then b else Γ.flatAtom b).isRight = true)) |> fun e => by
      convert e using 3 <;> split_ifs <;> simp_all
  · have hdeg : ∀ u, Γ'.nonDotDeg u = Γ.nonDotDeg u := by
      intro u
      unfold Graph.nonDotDeg
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      have e1 := List.countP_map (p := fun t : Kind × Atom 3 n × Atom 3 n =>
        decide ((t.2.1 = u ∨ t.2.2 = u) ∧ t.1 ≠ .dot ∧ t.1 ≠ .xdot)) (f := Local_tri)
        (l := Γ'.comps)
      have e2 := List.countP_map (p := fun t : Kind × Atom 3 n × Atom 3 n =>
        decide ((t.2.1 = u ∨ t.2.2 = u) ∧ t.1 ≠ .dot ∧ t.1 ≠ .xdot)) (f := Local_tri)
        (l := Γ.comps)
      unfold Local_Same3 at h
      rw [h.countP_eq] at e1
      exact e1.symm.trans e2
    have hdiff : ∀ u, Γ'.DiffToPinned u ↔ Γ.DiffToPinned u := by
      intro u
      unfold Graph.DiffToPinned
      rw [hu]
      exact Local_same3_all h (fun κ a b => κ.isDiffusive = true →
        (a = u → ¬ Γ.Unpinned b) ∧ (b = u → ¬ Γ.Unpinned a))
    have hhas : ∀ u, Γ'.HasDiffToPinned u ↔ Γ.HasDiffToPinned u := by
      intro u
      unfold Graph.HasDiffToPinned
      rw [hu]
      exact Local_same3_ex h (fun κ a b => κ.isDiffusive = true ∧
        (a = u ∧ ¬ Γ.Unpinned b ∨ b = u ∧ ¬ Γ.Unpinned a))
    unfold Graph.ExtClause
    rw [hb, hu, hdeg, hdeg, hhas, hhas, hdiff, hdiff,
      Local_same3_all h (fun κ a b => κ = .xdot → ¬ (Γ.Unpinned a ∧ Γ.Unpinned b)),
      Local_same3_all h (fun κ a b => κ.isDiffusive = true → a ≠ .inl 2 ∧ b ≠ .inl 2),
      Local_same3_ex h (fun κ a b => κ = .G .plus ∧ (a = .inl 1 ∨ b = .inl 1))]
  · unfold Graph.NoGhost
    exact Local_same3_all h (fun κ _ _ => κ ≠ .ghost)

/-! ### Graphs with the same components other than `×`-dotted edges -/

/-- The component is not a `×`-dotted edge. -/
private def Local_nx (c : Comp (Atom k n)) : Bool := c.kind != .xdot

/-- Two graphs whose components other than `×`-dotted edges agree in kinds and ends up to order. -/
private def Local_Same3X (Γ Γ' : Graph k n) : Prop :=
  ((Γ'.comps.filter Local_nx).map Local_tri).Perm ((Γ.comps.filter Local_nx).map Local_tri)

/-- The graph without its `×`-dotted edges. -/
private def Local_dropX (Γ : Graph k n) : Graph k n := ⟨Γ.comps.filter Local_nx, Γ.coeff⟩

private theorem Local_dropX_graphs (Γ : Graph k n) :
    (Local_dropX Γ).dotGraph = Γ.dotGraph ∧ (Local_dropX Γ).molGraph = Γ.molGraph := by
  have key : ∀ (P : Kind → Prop), (∀ κ, P κ → κ ≠ .xdot) → ∀ u v,
      (∃ c ∈ (Local_dropX Γ).comps, P c.kind ∧ c.x = u ∧ c.y = v) ↔
        (∃ c ∈ Γ.comps, P c.kind ∧ c.x = u ∧ c.y = v) := by
    intro P hP u v
    constructor
    · rintro ⟨c, hc, h⟩
      exact ⟨c, (List.mem_filter.1 hc).1, h⟩
    · rintro ⟨c, hc, h⟩
      exact ⟨c, List.mem_filter.2 ⟨hc, by simp [Local_nx, hP _ h.1]⟩, h⟩
  have hd : ∀ κ : Kind, κ = .dot → κ ≠ .xdot := by rintro κ rfl; simp
  have hm : ∀ κ : Kind, κ.joinsMol = true → κ ≠ .xdot := by rintro κ h rfl; simp [Kind.joinsMol] at h
  constructor
  · ext u v
    simp only [Graph.dotGraph, SimpleGraph.fromRel_adj]
    rw [key _ hd u v, key _ hd v u]
  · ext u v
    simp only [Graph.molGraph, SimpleGraph.fromRel_adj]
    rw [key _ hm u v, key _ hm v u]

private theorem Local_same3X_dropX {Γ Γ' : Graph k n} (h : Local_Same3X Γ Γ') :
    Local_Same3 (Local_dropX Γ) (Local_dropX Γ') := h

/-- A graph and the graph without its `×`-dotted edges carry each other. -/
private theorem Local_dropX_carry [NeZero k] (Γ : Graph k n) :
    Local_Carry Γ.toMG' (Local_dropX Γ).toMG' id ∧ Local_Carry (Local_dropX Γ).toMG' Γ.toMG' id := by
  obtain ⟨hd, hm⟩ := Local_dropX_graphs Γ
  have hr := Local_graphs_rho hd hm
  have hint : (Local_dropX Γ).toMG'.int = Γ.toMG'.int := by
    simp only [Graph.toMG', (Local_graphs_fun hd hm).2.2.2.1]
  have hperm := (List.filter_append_perm Local_nx Γ.comps)
  have habs : ∀ c ∈ Γ.comps.filter (fun c => !Local_nx c), (Local_rd Γ c).1 = none := by
    intro c hc
    have := (List.mem_filter.1 hc).2
    have hx : c.kind = .xdot := by simpa [Local_nx] using this
    simp [Local_rd, hx, Kind.mclass]
  have e : Local_Carry (Local_RG Γ (Γ.comps.filter Local_nx))
      (Local_RG (Local_dropX Γ) (Local_dropX Γ).comps) id := by
    unfold Local_RG
    rw [hint, hr.2.2, hr.2.1]
    exact Local_carry_refl _
  have e' : Local_Carry (Local_RG (Local_dropX Γ) (Local_dropX Γ).comps)
      (Local_RG Γ (Γ.comps.filter Local_nx)) id := by
    unfold Local_RG
    rw [hint, hr.2.2, hr.2.1]
    exact Local_carry_refl _
  constructor
  · exact Local_carry_trans_id (Local_carry_toRG Γ) (Local_carry_trans_id
      (Local_RG_perm Γ hperm.symm) (Local_carry_trans_id (Local_RG_drop Γ habs)
        (Local_carry_trans_id e (Local_carry_ofRG _))))
  · exact Local_carry_trans_id (Local_carry_toRG _) (Local_carry_trans_id e'
      (Local_carry_trans_id (Local_RG_append Γ habs) (Local_carry_trans_id
        (Local_RG_perm Γ hperm) (Local_carry_ofRG Γ))))

private theorem Local_same3X_fun {Γ Γ' : Graph k n} (h : Local_Same3X Γ Γ') :
    Γ'.SameBlock = Γ.SameBlock ∧ Γ'.SameMol = Γ.SameMol ∧ Γ'.anchor = Γ.anchor ∧
      Γ'.molRep = Γ.molRep ∧ Γ'.flatAtom = Γ.flatAtom ∧ Γ'.Unpinned = Γ.Unpinned := by
  obtain ⟨d1, m1⟩ := Local_dropX_graphs Γ
  obtain ⟨d2, m2⟩ := Local_dropX_graphs Γ'
  obtain ⟨d3, m3⟩ := Local_same3_graphs (Local_same3X_dropX h)
  exact Local_graphs_fun (d2.symm.trans (d3.trans d1)) (m2.symm.trans (m3.trans m1))

private theorem Local_same3X_carry [NeZero k] {Γ Γ' : Graph k n} (h : Local_Same3X Γ Γ') :
    Local_Carry Γ.toMG' Γ'.toMG' id :=
  Local_carry_trans_id (Local_dropX_carry Γ).1 (Local_carry_trans_id
    (Local_same3_carry (Local_same3X_dropX h)) (Local_dropX_carry Γ').2)

end Tri

/-! ## Terms of the local expansions with new atoms in the molecule of `x` -/

section Dec

variable {n : ℕ}

/-- The component without its label. -/
private def Local_stripC {V : Type} (c : Comp V) : Comp V := { c with label := none }

/-- The graph without labels. -/
private def Local_strip {k : ℕ} (Γ : Graph k n) : Graph k n := ⟨Γ.comps.map Local_stripC, Γ.coeff⟩

private theorem Local_strip_same3 {k : ℕ} (Γ : Graph k n) : Local_Same3 Γ (Local_strip Γ) := by
  unfold Local_Same3
  rw [show (Local_strip Γ).comps.map Local_tri = Γ.comps.map Local_tri by
    simp [Local_strip, Local_tri, Local_stripC, Function.comp_def]]

/-- A component `d` of the graph replaced in the term by `d'` of the same random kind (or both
weights), with the same external ends, internal ends at internal atoms, and the same reading. -/
private def Local_MovR (Γ : Graph 3 n) (x : Fin n) (j : ℕ) (d : Comp (Atom 3 n))
    (d' : Comp (Atom 3 (n + j))) : Prop :=
  (d'.kind = d.kind ∨ (d.kind.isWeight = true ∧ d'.kind.isWeight = true)) ∧ d.kind.isRandom = true ∧
    (d'.x = liftA j d.x ∨ (d.x.isRight = true ∧ d'.x.isRight = true)) ∧
    (d'.y = liftA j d.y ∨ (d.y.isRight = true ∧ d'.y.isRight = true)) ∧
    Local_SameR Γ d (d'.map (Local_proj j x))

/-- A new component of the term: between internal atoms, neither dotted, `×`-dotted, ghost nor
diffusive, absent in the reading, and joining atoms read in the molecule of `x` if it is waved. -/
private def Local_NewOK (Γ : Graph 3 n) (x : Fin n) (j : ℕ) (c : Comp (Atom 3 (n + j))) : Prop :=
  c.x.isRight = true ∧ c.y.isRight = true ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot ∧ c.kind ≠ .ghost ∧
    c.kind.isDiffusive = false ∧ (Local_rd Γ (c.map (Local_proj j x))).1 = none ∧
    (c.kind.joinsMol = true → Γ.SameMol (Local_proj j x c.x) (.inr x) ∧
      Γ.SameMol (Local_proj j x c.y) (.inr x))

/-- No path, or one random component `c` replaced by the two factors of `-∂_{h_{uv}} c` (in either
order of the factors) with `u`, `v` internal atoms read in the molecule of `x`. -/
private def Local_PathOK (Γ : Graph 3 n) (x : Fin n) (j : ℕ) (P : List (Comp (Atom 3 n)))
    (P' : List (Comp (Atom 3 (n + j)))) : Prop :=
  (P = [] ∧ P' = []) ∨ ∃ (c : Comp (Atom 3 n)) (ch : Charge) (u v : Atom 3 (n + j)), P = [c] ∧
    (c.kind = .G ch ∨ c.kind = .weight ch ∨ c.kind = .light ch) ∧
    u.isRight = true ∧ v.isRight = true ∧ Γ.SameMol (Local_proj j x u) (.inr x) ∧
    Γ.SameMol (Local_proj j x v) (.inr x) ∧
    P'.Perm [solidC ch (liftA j c.x) u,
      solidC ch v (liftA j (if c.kind.isWeight then c.x else c.y))]

/-- The term `Γ'` of a local expansion at `x` with `j` new atoms, up to labels and the order of
the components: the components `K` of `Γ` kept, the components `D` replaced one by one by `D'`, at
most one path, the weights `R` removed, the new components `N`, every new atom joined to `x`. -/
private def Local_Dec (Γ : Graph 3 n) (x : Fin n) (j : ℕ) (Γ' : Graph 3 (n + j)) : Prop :=
  ∃ (K D P R : List (Comp (Atom 3 n))) (D' P' N : List (Comp (Atom 3 (n + j)))),
    (Γ.comps.map Local_stripC).Perm (K ++ D ++ P ++ R) ∧
    (liftCs j K ++ D' ++ P' ++ N).Perm (Γ'.comps.map Local_stripC) ∧
    List.Forall₂ (Local_MovR Γ x j) D D' ∧ Local_PathOK Γ x j P P' ∧
    (∀ c ∈ R, c.kind.isWeight = true) ∧ (∀ c ∈ N, Local_NewOK Γ x j c) ∧
    ∀ i : Fin j, Γ'.molGraph.Reachable (newA i) (liftA j (.inr x))

end Dec

section DecMain

variable {n : ℕ}

private theorem Local_f2_left {α β : Type*} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {a : α} (ha : a ∈ l) : ∃ b ∈ l', R a b := by
  induction h with
  | nil => simp at ha
  | cons hr _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨b, hb, h⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

private theorem Local_f2_right {α β : Type*} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {b : β} (hb : b ∈ l') : ∃ a ∈ l, R a b := by
  induction h with
  | nil => simp at hb
  | cons hr _ ih =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨a, ha, h⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

private theorem Local_countP_f2 {α β : Type*} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {p : α → Bool} {p' : β → Bool}
    (hp : ∀ a b, R a b → p' b = true → p a = true) : l'.countP p' ≤ l.countP p := by
  induction h with
  | nil => simp
  | @cons a b l l' hr _ ih =>
    simp only [List.countP_cons]
    refine Nat.add_le_add ih ?_
    by_cases hq : p' b = true
    · simp [hq, hp a b hr hq]
    · simp [hq]

private theorem Local_mem_liftCs {j : ℕ} {K : List (Comp (Atom 3 n))} {c' : Comp (Atom 3 (n + j))} :
    c' ∈ liftCs j K ↔ ∃ c ∈ K, c' = c.map (liftA j) := by
  simp only [liftCs, List.mem_map]
  exact ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, h.symm⟩, fun ⟨c, hc, h⟩ => ⟨c, hc, h.symm⟩⟩

private theorem Local_kind_solidC {V : Type} [DecidableEq V] (ch : Charge) (a b : V) :
    (solidC ch a b).kind = .G ch ∨ (solidC ch a b).kind = .weight ch := by
  unfold solidC
  split_ifs <;> simp [mkC]

private theorem Local_isRandom_kinds {κ : Kind} (h : κ.isRandom = true) :
    κ ≠ .dot ∧ κ ≠ .xdot ∧ κ.joinsMol = false ∧ κ.isDiffusive = false ∧ κ ≠ .ghost := by
  cases κ <;> simp_all [Kind.isRandom, Kind.joinsMol, Kind.isDiffusive]

private theorem Local_weight_random {κ : Kind} (h : κ.isWeight = true) : κ.isRandom = true := by
  cases κ <;> simp_all [Kind.isWeight, Kind.isRandom]

private theorem Local_movR_random {κ κ' : Kind} (hk : κ' = κ ∨ (κ.isWeight = true ∧ κ'.isWeight = true))
    (hr : κ.isRandom = true) : κ'.isRandom = true := by
  rcases hk with rfl | ⟨-, h⟩
  · exact hr
  · exact Local_weight_random h

private theorem Local_diff_notRandom {κ : Kind} (h : κ.isDiffusive = true) :
    κ.isRandom = false := by
  cases κ <;> simp_all [Kind.isDiffusive, Kind.isRandom]

private theorem Local_solidC_random {V : Type} [DecidableEq V] (ch : Charge) (a b : V) :
    (solidC ch a b).kind.isRandom = true := by
  rcases Local_kind_solidC ch a b with h | h <;> rw [h] <;> rfl

private theorem Local_pathOK_random {Γ : Graph 3 n} {x : Fin n} {j : ℕ}
    {P : List (Comp (Atom 3 n))} {P' : List (Comp (Atom 3 (n + j)))}
    (h : Local_PathOK Γ x j P P') :
    (∀ c ∈ P, c.kind.isRandom = true) ∧ ∀ c' ∈ P', c'.kind.isRandom = true := by
  rcases h with ⟨rfl, rfl⟩ | ⟨c, ch, u, v, rfl, hk, -, -, -, -, hp⟩
  · simp
  · refine ⟨fun c' hc' => ?_, fun c' hc' => ?_⟩
    · simp only [List.mem_singleton] at hc'
      subst hc'
      rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
    · rw [hp.mem_iff] at hc'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl <;> exact Local_solidC_random _ _ _

/-- The decomposition of `Local_Dec` gives `Local_LiftOK` for the graphs without labels. -/
private theorem Local_dec_liftOK {Γ : Graph 3 n} {x : Fin n} {j : ℕ} {Γ' : Graph 3 (n + j)}
    {K D P R : List (Comp (Atom 3 n))} {D' P' N : List (Comp (Atom 3 (n + j)))}
    (h1 : (Γ.comps.map Local_stripC).Perm (K ++ D ++ P ++ R))
    (h2 : (liftCs j K ++ D' ++ P' ++ N).Perm (Γ'.comps.map Local_stripC))
    (h3 : List.Forall₂ (Local_MovR Γ x j) D D') (h4 : Local_PathOK Γ x j P P')
    (h5 : ∀ c ∈ R, c.kind.isWeight = true) (h6 : ∀ c ∈ N, Local_NewOK Γ x j c)
    (h7 : ∀ i : Fin j, Γ'.molGraph.Reachable (newA i) (liftA j (.inr x))) :
    Local_LiftOK (Local_strip Γ) x j (Local_strip Γ') := by
  have hS := Local_same3_fun (Local_strip_same3 Γ)
  have hS' := Local_same3_fun (Local_strip_same3 Γ')
  obtain ⟨hPr, hP'r⟩ := Local_pathOK_random h4
  have hDr : ∀ d ∈ D, d.kind.isRandom = true := fun d hd => by
    obtain ⟨d', -, hm⟩ := Local_f2_left h3 hd
    exact hm.2.1
  have hD'r : ∀ d' ∈ D', d'.kind.isRandom = true := fun d' hd' => by
    obtain ⟨d, -, hm⟩ := Local_f2_right h3 hd'
    exact Local_movR_random hm.1 hm.2.1
  have hRr : ∀ c ∈ R, c.kind.isRandom = true := fun c hc => by
    have := h5 c hc
    cases hk : c.kind <;> simp_all [Kind.isWeight, Kind.isRandom]
  -- a component of `Γ` that is not random lies in `K`
  have inK : ∀ c ∈ (Local_strip Γ).comps, c.kind.isRandom = false → c ∈ K := by
    intro c hc hr
    have := h1.mem_iff.1 hc
    simp only [List.mem_append] at this
    rcases this with ((h | h) | h) | h
    · exact h
    · exact absurd (hDr c h) (by rw [hr]; simp)
    · exact absurd (hPr c h) (by rw [hr]; simp)
    · exact absurd (hRr c h) (by rw [hr]; simp)
  -- a component of `Γ'` that is not random lies in `liftCs j K` or in `N`
  have inK' : ∀ c' ∈ (Local_strip Γ').comps, c'.kind.isRandom = false →
      c' ∈ liftCs j K ∨ c' ∈ N := by
    intro c' hc' hr
    have := h2.symm.mem_iff.1 hc'
    simp only [List.mem_append] at this
    rcases this with ((h | h) | h) | h
    · exact Or.inl h
    · exact absurd (hD'r c' h) (by rw [hr]; simp)
    · exact absurd (hP'r c' h) (by rw [hr]; simp)
    · exact Or.inr h
  have liftmem : ∀ c ∈ K, c.map (liftA j) ∈ (Local_strip Γ').comps := fun c hc =>
    h2.mem_iff.1 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (Local_mem_liftCs.2 ⟨c, hc, rfl⟩))))
  have Kmem : ∀ c ∈ K, c ∈ (Local_strip Γ).comps := fun c hc =>
    h1.symm.mem_iff.1 (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ hc)))
  have nr_dot : ∀ κ : Kind, κ = .dot → κ.isRandom = false := by rintro κ rfl; rfl
  have nr_mol : ∀ κ : Kind, κ.joinsMol = true → κ.isRandom = false := by
    intro κ h; cases κ <;> simp_all [Kind.joinsMol, Kind.isRandom]
  refine ⟨fun c hc hk => ?_, fun c' hc' hk => ?_, fun c hc hk => ?_, fun c' hc' hk => ?_,
    fun i => ?_⟩
  · exact ⟨_, liftmem c (inK c hc (nr_dot _ hk)), hk, rfl, rfl⟩
  · rcases inK' c' hc' (nr_dot _ hk) with h | h
    · obtain ⟨c, hc, rfl⟩ := Local_mem_liftCs.1 h
      exact ⟨c, Kmem c hc, hk, rfl, rfl⟩
    · exact absurd hk (h6 c' h).2.2.1
  · exact ⟨_, liftmem c (inK c hc (nr_mol _ hk)), hk, rfl, rfl⟩
  · rcases inK' c' hc' (nr_mol _ hk) with h | h
    · obtain ⟨c, hc, rfl⟩ := Local_mem_liftCs.1 h
      exact Or.inl ⟨c, Kmem c hc, hk, rfl, rfl⟩
    · right
      rw [hS.2.1]
      exact (h6 c' h).2.2.2.2.2.2.2 hk
  · have e : (Local_strip Γ').molGraph = Γ'.molGraph := by
      ext u v
      have := hS'.2.1
      simp only [Graph.molGraph, SimpleGraph.fromRel_adj]
      rw [Local_same3_ex (Local_strip_same3 Γ') (fun κ a b => κ.joinsMol = true ∧ a = u ∧ b = v),
        Local_same3_ex (Local_strip_same3 Γ') (fun κ a b => κ.joinsMol = true ∧ a = v ∧ b = u)]
    rw [e]
    exact h7 i

/-- On a graph with the charge pattern of the block normal form, the first atom of a random
component is internal in the block normal form. -/
private theorem Local_colour_x {Γ : Graph 3 n} (h : Γ.ColourInvB) {c : Comp (Atom 3 n)}
    (hc : c ∈ Γ.comps) (hr : c.kind.isRandom = true) : (Γ.flatAtom c.x).isRight = true := by
  have hk : c.kind ≠ .dot := (Local_isRandom_kinds hr).1
  unfold Graph.ColourInvB Graph.ColourInv' at h
  have := ((h _ (List.mem_map_of_mem (f := Γ.flatComp) hc)).1 (by rw [Graph.flatComp_kind]; exact hr)).1
  simpa [Graph.flatComp, hk] using this

private theorem Local_rho_int {k : ℕ} {Γ : Graph k n} {u : Atom k n}
    (h : (Γ.flatAtom u).isRight = true) : Local_rho Γ u ∈ Γ.toMG'.int := by
  unfold Local_rho
  rcases hf : Γ.flatAtom u with a | b
  · rw [hf] at h; simp at h
  · exact Local_mem_int.2 ⟨b, rfl⟩

/-- The blue or red class of the solid edges of charge `ch`. -/
private def Local_mOf : Charge → MClass
  | .plus => .plus
  | .minus => .minus

private theorem Local_mclass_G (ch : Charge) : (Kind.G ch).mclass = some (Local_mOf ch) := by
  cases ch <;> rfl

private theorem Local_mclass_minus {κ : Kind} (h : κ.mclass = some .minus) : κ = .G .minus := by
  cases κ with
  | G ch => cases ch <;> simp_all [Kind.mclass]
  | aux j r b => cases b <;> simp_all [Kind.mclass]
  | _ => simp_all [Kind.mclass]

private theorem Local_mOf_cases (ch : Charge) : Local_mOf ch = .plus ∨ Local_mOf ch = .minus := by
  cases ch <;> simp [Local_mOf]

private theorem Local_rd_solidC {k m : ℕ} (Γ : Graph k n) (f : Atom k m → Atom k n) (ch : Charge)
    (a b : Atom k m) :
    Local_rd Γ ((solidC ch a b).map f) = Local_pe (Local_mOf ch) (Local_rho Γ (f a))
      (Local_rho Γ (f b)) := by
  unfold solidC
  split_ifs with hab
  · subst hab
    simp [Local_rd, Local_pe, mkC, Comp.map]
  · simp only [Local_rd, Local_pe, mkC, Comp.map]
    by_cases he : Local_rho Γ (f a) = Local_rho Γ (f b)
    · simp [he]
    · simp [he, Local_mclass_G]

/-- An internal atom read in the molecule of `x` is read at the representative of `x`. -/
private theorem Local_rho_molx {k : ℕ} {Γ : Graph k n} {x : Fin n} {u : Atom k n}
    (h : Γ.SameMol u (.inr x)) : Local_rho Γ u = Γ.molRep (.inr x) := by
  have hu : u.isRight = true := by
    rcases h with rfl | ⟨h1, -⟩
    · rfl
    · exact h1
  obtain ⟨b, rfl⟩ : ∃ b, u = .inr b := by
    cases u with
    | inl a => simp at hu
    | inr b => exact ⟨b, rfl⟩
  exact (Local_molRep_eq_iff Γ _ _).2 h

/-- The molecular graph of a term of `Local_Dec` is carried from that of the graph along
`liftA j`. -/
private theorem Local_dec_carry {Γ : Graph 3 n} {x : Fin n} {j : ℕ} {Γ' : Graph 3 (n + j)}
    (hd : Local_Dec Γ x j Γ') (hC : Γ.ColourInvB) :
    Local_Carry Γ.toMG' Γ'.toMG' (liftA j) := by
  obtain ⟨K, D, P, R, D', P', N, h1, h2, h3, h4, h5, h6, h7⟩ := hd
  have hL := Local_dec_liftOK h1 h2 h3 h4 h5 h6 h7
  have hs3 := Local_strip_same3 Γ
  have hr3 := Local_same3_rho hs3
  have hf3 := Local_same3_fun hs3
  have hSR : ∀ c c', Local_SameR Γ c c' → Local_SameR (Local_strip Γ) c c' := by
    intro c c' h
    unfold Local_SameR
    rw [hr3.2.1]
    exact h
  have hlift : (liftCs j K).map (Comp.map (Local_proj j x)) = K := by
    simp [liftCs, Function.comp_def, Local_comp_proj_lift]
  have hmapπ := (h2.map (Comp.map (Local_proj j x)))
  simp only [List.map_append, hlift] at hmapπ
  have hRabs : ∀ c ∈ R, (Local_rd (Local_strip Γ) c).1 = none := by
    intro c hc
    have hw := h5 c hc
    have : c.kind.mclass = none := by
      cases hk : c.kind <;> simp_all [Kind.isWeight, Kind.mclass]
    simp [Local_rd, this]
  have hNabs : ∀ c ∈ N.map (Comp.map (Local_proj j x)), (Local_rd (Local_strip Γ) c).1 = none := by
    intro c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    rw [hr3.2.1]
    exact (h6 c' hc').2.2.2.2.2.2.1
  have hDD : List.Forall₂ (Local_SameR (Local_strip Γ)) D (D'.map (Comp.map (Local_proj j x))) := by
    rw [List.forall₂_map_right_iff]
    exact h3.imp (fun d d' hm => hSR _ _ hm.2.2.2.2)
  have hmid : Local_Carry (Local_RG (Local_strip Γ) (Local_strip Γ).comps)
      (Local_RG (Local_strip Γ) ((Local_strip Γ').comps.map (Comp.map (Local_proj j x)))) id := by
    rcases h4 with ⟨rfl, rfl⟩ | ⟨c, ch, u, v, rfl, hk, hu, hv, hux, hvx, hp⟩
    · simp only [List.append_nil, List.map_nil] at h1 hmapπ
      exact Local_RG_shape (Local_strip Γ) h1 hmapπ hDD hRabs hNabs
    · have hcΓ : c ∈ (Local_strip Γ).comps := h1.symm.mem_iff.1 (by simp)
      have hcr : c.kind.isRandom = true := by rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
      obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hcΓ
      have hcx : (Γ.flatAtom c₀.x).isRight = true := Local_colour_x hC hc₀ hcr
      have hP' := hp.map (Comp.map (Local_proj j x))
      simp only [List.map_cons, List.map_nil] at hP'
      have e1 : (liftA j (Local_stripC c₀).x).isRight = (Local_stripC c₀).x.isRight :=
        Local_lift_isRight j _
      refine Local_RG_shapeP (Local_strip Γ) (c := Local_stripC c₀)
        (p₁ := (solidC ch (liftA j (Local_stripC c₀).x) u).map (Local_proj j x))
        (p₂ := (solidC ch v (liftA j (if (Local_stripC c₀).kind.isWeight then (Local_stripC c₀).x
          else (Local_stripC c₀).y))).map (Local_proj j x))
        (m := Local_mOf ch) (A := Local_rho (Local_strip Γ) (Local_stripC c₀).x)
        (X := (Local_strip Γ).molRep (.inr x))
        (B := Local_rho (Local_strip Γ) (if (Local_stripC c₀).kind.isWeight then (Local_stripC c₀).x
          else (Local_stripC c₀).y)) h1
        ((List.Perm.append_right _ (List.Perm.append_left _ hP'.symm)).trans hmapπ) hDD hRabs
        hNabs (Local_mOf_cases ch) ?_ ?_ (Local_rho_vtx _ _) ?_ ?_ ?_
      · refine Local_rho_int ?_
        rw [hf3.2.2.2.2.1]
        exact hcx
      · exact Local_mem_int.2 ⟨x, rfl⟩
      · -- the component `c` reads as the edge from `A` to `B`
        rcases hk with hk | hk | hk
        · have hw : (Local_stripC c₀).kind.isWeight = false := by rw [hk]; rfl
          simp only [hw, Bool.false_eq_true, if_false]
          refine Or.inr ⟨?_, Or.inl rfl⟩
          simp only [Local_rd, Local_pe, hk]
          by_cases he : Local_rho (Local_strip Γ) (Local_stripC c₀).x = Local_rho (Local_strip Γ) (Local_stripC c₀).y
          · simp [he]
          · simp [he, Local_mclass_G]
        all_goals
          have hw : (Local_stripC c₀).kind.isWeight = true := by rw [hk]; rfl
          simp only [hw, if_true]
          left
          refine ⟨?_, by simp [Local_pe]⟩
          simp [Local_rd, hk, Kind.mclass]
      · rw [Local_rd_solidC, Local_proj_lift,
          Local_rho_molx (u := Local_proj j x u) (by rw [hf3.2.1]; exact hux), hf3.2.2.2.1]
      · rw [Local_rd_solidC, Local_proj_lift,
          Local_rho_molx (u := Local_proj j x v) (by rw [hf3.2.1]; exact hvx), hf3.2.2.2.1]
  have hend := Local_carry_lift hL
  have hstart := Local_carry_toRG (Local_strip Γ)
  have h0 := Local_same3_carry hs3
  have h9 := Local_same3_carry (Local_same3_symm (Local_strip_same3 Γ'))
  have hc := Local_carry_trans h0 (Local_carry_trans hstart (Local_carry_trans hmid
    (Local_carry_trans hend h9)))
  exact hc

/-- The charge pattern of the block normal form, component by component. -/
private def Local_CC (Γ : Graph 3 n) (c : Comp (Atom 3 n)) : Prop :=
  (c.kind.isRandom = true → (Γ.flatAtom c.x).isRight = true ∧ Γ.flatAtom c.y ≠ .inl 0 ∧
    (Γ.flatAtom c.y = .inl 1 → c.kind = .G .plus) ∧ (Γ.flatAtom c.y = .inl 2 → c.kind = .G .minus)) ∧
  (c.kind = .waved .s → (Γ.flatAtom c.x).isRight = true ∧ (Γ.flatAtom c.y).isRight = true)

private theorem Local_colour_iff (Γ : Graph 3 n) : Γ.ColourInvB ↔ ∀ c ∈ Γ.comps, Local_CC Γ c := by
  unfold Graph.ColourInvB Graph.ColourInv' Graph.blockNorm
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun c _ => ?_
  by_cases hk : c.kind = .dot
  · simp [Graph.flatComp, hk, Local_CC, Kind.isRandom]
  · simp [Graph.flatComp, hk, Local_CC]

/-- A component between internal atoms satisfies the charge pattern unless it is random with an
external first atom. -/
private theorem Local_CC_int {Γ : Graph 3 n} {c : Comp (Atom 3 n)} (hx : c.x.isRight = true)
    (hy : c.y.isRight = true) : Local_CC Γ c := by
  obtain ⟨a, ha⟩ : ∃ a, c.x = .inr a := by
    cases h : c.x with
    | inl a => rw [h] at hx; simp at hx
    | inr a => exact ⟨a, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, c.y = .inr b := by
    cases h : c.y with
    | inl a => rw [h] at hy; simp at hy
    | inr b => exact ⟨b, rfl⟩
  have e1 : Γ.flatAtom c.x = .inr a := by rw [ha]; rfl
  have e2 : Γ.flatAtom c.y = .inr b := by rw [hb]; rfl
  simp [Local_CC, e1, e2]

/-- The clauses of a term of `Local_Dec` on the graphs without labels. -/
private theorem Local_dec_clauses_strip {Γ : Graph 3 n} {x : Fin n} {j : ℕ} {Γ' : Graph 3 (n + j)}
    {K D P R : List (Comp (Atom 3 n))} {D' P' N : List (Comp (Atom 3 (n + j)))}
    (h1 : (Γ.comps.map Local_stripC).Perm (K ++ D ++ P ++ R))
    (h2 : (liftCs j K ++ D' ++ P' ++ N).Perm (Γ'.comps.map Local_stripC))
    (h3 : List.Forall₂ (Local_MovR Γ x j) D D') (h4 : Local_PathOK Γ x j P P')
    (h5 : ∀ c ∈ R, c.kind.isWeight = true) (h6 : ∀ c ∈ N, Local_NewOK Γ x j c)
    (hL : Local_LiftOK (Local_strip Γ) x j (Local_strip Γ'))
    (hC : (Local_strip Γ).ColourInvB) (hE : (Local_strip Γ).ExtClause)
    (hG : (Local_strip Γ).NoGhost) :
    (Local_strip Γ').ColourInvB ∧ (Local_strip Γ').ExtClause ∧ (Local_strip Γ').NoGhost := by
  set Γs := Local_strip Γ with hΓs
  set Γ's := Local_strip Γ' with hΓ's
  have hc1 : Γs.comps.Perm (K ++ D ++ P ++ R) := h1
  have hc2 : (liftCs j K ++ D' ++ P' ++ N).Perm Γ's.comps := h2
  obtain ⟨hPr, hP'r⟩ := Local_pathOK_random h4
  have hDr : ∀ d ∈ D, d.kind.isRandom = true := fun d hd => by
    obtain ⟨d', -, hm⟩ := Local_f2_left h3 hd
    exact hm.2.1
  have hD'r : ∀ d' ∈ D', d'.kind.isRandom = true := fun d' hd' => by
    obtain ⟨d, -, hm⟩ := Local_f2_right h3 hd'
    exact Local_movR_random hm.1 hm.2.1
  have hRr : ∀ c ∈ R, c.kind.isRandom = true := fun c hc => by
    have := h5 c hc
    cases hk : c.kind <;> simp_all [Kind.isWeight, Kind.isRandom]
  have memΓ : ∀ c ∈ K ++ D ++ P ++ R, c ∈ Γs.comps := fun c hc => hc1.symm.mem_iff.1 hc
  have memΓ' : ∀ c' ∈ Γ's.comps, c' ∈ liftCs j K ∨ c' ∈ D' ∨ c' ∈ P' ∨ c' ∈ N := by
    intro c' hc'
    have := hc2.mem_iff.2 hc'
    simp only [List.mem_append] at this
    tauto
  have liftmem : ∀ c ∈ K, c.map (liftA j) ∈ Γ's.comps := fun c hc =>
    hc2.mem_iff.1 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (Local_mem_liftCs.2 ⟨c, hc, rfl⟩))))
  have inK : ∀ c ∈ Γs.comps, c.kind.isRandom = false → c ∈ K := by
    intro c hc hr
    have := hc1.mem_iff.1 hc
    simp only [List.mem_append] at this
    rcases this with ((h | h) | h) | h
    · exact h
    · exact absurd (hDr c h) (by rw [hr]; simp)
    · exact absurd (hPr c h) (by rw [hr]; simp)
    · exact absurd (hRr c h) (by rw [hr]; simp)
  have flatL := Local_lift_flat hL
  have unpL := Local_lift_unpinned hL
  have inl_iff : ∀ (u : Atom 3 n) (a : Fin 3), liftA j u = .inl a ↔ u = .inl a := by
    intro u a
    cases u <;> simp [liftA]
  have flat_int : ∀ u : Atom 3 (n + j), u.isRight = true → Γ's.flatAtom u = u := by
    intro u hu
    cases u with
    | inl a => simp at hu
    | inr b => rfl
  have isR_ne : ∀ (u : Atom 3 (n + j)) (a : Fin 3), u.isRight = true → u ≠ .inl a := by
    rintro u a hu rfl
    simp at hu
  have hCC := (Local_colour_iff Γs).1 hC
  -- the charge pattern
  have CClift : ∀ c, Local_CC Γs c → Local_CC Γ's (c.map (liftA j)) := by
    intro c h
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hr => ?_, fun hw => ?_⟩
    · obtain ⟨a1, a2, a3, a4⟩ := h1 hr
      refine ⟨?_, ?_, ?_, ?_⟩
      · change (Γ's.flatAtom (liftA j c.x)).isRight = true
        rw [flatL, Local_lift_isRight]
        exact a1
      · change Γ's.flatAtom (liftA j c.y) ≠ _
        rw [flatL, Ne, inl_iff]
        exact a2
      · change Γ's.flatAtom (liftA j c.y) = _ → _
        rw [flatL, inl_iff]
        exact a3
      · change Γ's.flatAtom (liftA j c.y) = _ → _
        rw [flatL, inl_iff]
        exact a4
    · obtain ⟨a1, a2⟩ := h2 hw
      refine ⟨?_, ?_⟩
      · change (Γ's.flatAtom (liftA j c.x)).isRight = true
        rw [flatL, Local_lift_isRight]
        exact a1
      · change (Γ's.flatAtom (liftA j c.y)).isRight = true
        rw [flatL, Local_lift_isRight]
        exact a2
  have hColour : Γ's.ColourInvB := by
    refine (Local_colour_iff Γ's).2 fun c' hc' => ?_
    rcases memΓ' c' hc' with h | h | h | h
    · obtain ⟨c, hc, rfl⟩ := Local_mem_liftCs.1 h
      exact CClift c (hCC c (memΓ c (by simp [hc])))
    · obtain ⟨d, hd, hk, hr, hx, hy, -⟩ := Local_f2_right h3 h
      obtain ⟨b1, b2⟩ := hCC d (memΓ d (by simp [hd]))
      obtain ⟨a1, a2, a3, a4⟩ := b1 hr
      have hr' := Local_movR_random hk hr
      have hkk : ∀ ch, d.kind = .G ch → c'.kind = .G ch := by
        intro ch h'
        rcases hk with hk | ⟨hw, -⟩
        · rw [hk, h']
        · rw [h'] at hw; simp [Kind.isWeight] at hw
      refine ⟨fun _ => ⟨?_, ?_, ?_, ?_⟩, fun hw => absurd hr' (by rw [hw]; simp [Kind.isRandom])⟩
      · rcases hx with hx | ⟨-, hx⟩
        · rw [hx, flatL, Local_lift_isRight]; exact a1
        · rw [flat_int _ hx]; exact hx
      · rcases hy with hy | ⟨-, hy⟩
        · rw [hy, flatL, Ne, inl_iff]; exact a2
        · rw [flat_int _ hy]; exact isR_ne _ _ hy
      · rcases hy with hy | ⟨-, hy⟩
        · rw [hy, flatL, inl_iff]; exact fun h' => hkk _ (a3 h')
        · rw [flat_int _ hy]; exact fun h => absurd h (isR_ne _ _ hy)
      · rcases hy with hy | ⟨-, hy⟩
        · rw [hy, flatL, inl_iff]; exact fun h' => hkk _ (a4 h')
        · rw [flat_int _ hy]; exact fun h => absurd h (isR_ne _ _ hy)
    · rcases h4 with ⟨-, rfl⟩ | ⟨c, ch, u, v, rfl, hk, hu, hv, -, -, hp⟩
      · simp at h
      · have hcΓ : c ∈ Γs.comps := memΓ c (by simp)
        have hcr : c.kind.isRandom = true := by rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
        obtain ⟨b1, -⟩ := hCC c hcΓ
        obtain ⟨a1, a2, a3, a4⟩ := b1 hcr
        set b := (if c.kind.isWeight then c.x else c.y) with hbdef
        have hbf : Γs.flatAtom b ≠ .inl 0 ∧ (Γs.flatAtom b = .inl 1 → ch = .plus) ∧
            (Γs.flatAtom b = .inl 2 → ch = .minus) := by
          rcases hk with hk | hk | hk
          · have hw : c.kind.isWeight = false := by rw [hk]; rfl
            have hbe : b = c.y := by simp [hbdef, hw]
            rw [hbe]
            refine ⟨a2, fun h => ?_, fun h => ?_⟩
            · have := a3 h; rw [hk] at this; simpa using this
            · have := a4 h; rw [hk] at this; simpa using this
          all_goals
            have hw : c.kind.isWeight = true := by rw [hk]; rfl
            have hbe : b = c.x := by simp [hbdef, hw]
            rw [hbe]
            refine ⟨fun h => by rw [h] at a1; simp at a1, fun h => by rw [h] at a1; simp at a1,
              fun h => by rw [h] at a1; simp at a1⟩
        rw [hp.mem_iff] at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · unfold solidC
          split_ifs with he
          · rw [he]
            exact Local_CC_int hu hu
          · refine ⟨fun _ => ⟨?_, ?_, ?_, ?_⟩, fun hw => by simp [mkC] at hw⟩
            · change (Γ's.flatAtom (liftA j c.x)).isRight = true
              rw [flatL, Local_lift_isRight]; exact a1
            · change Γ's.flatAtom u ≠ _
              rw [flat_int _ hu]; exact isR_ne _ _ hu
            · change Γ's.flatAtom u = _ → _
              rw [flat_int _ hu]; exact fun h => absurd h (isR_ne _ _ hu)
            · change Γ's.flatAtom u = _ → _
              rw [flat_int _ hu]; exact fun h => absurd h (isR_ne _ _ hu)
        · unfold solidC
          split_ifs with he
          · exact Local_CC_int hv hv
          · refine ⟨fun _ => ⟨?_, ?_, ?_, ?_⟩, fun hw => by simp [mkC] at hw⟩
            · change (Γ's.flatAtom v).isRight = true
              rw [flat_int _ hv]; exact hv
            · change Γ's.flatAtom (liftA j b) ≠ _
              rw [flatL, Ne, inl_iff]
              exact hbf.1
            · change Γ's.flatAtom (liftA j b) = _ → _
              rw [flatL, inl_iff]
              intro h
              simp [mkC, hbf.2.1 h]
            · change Γ's.flatAtom (liftA j b) = _ → _
              rw [flatL, inl_iff]
              intro h
              simp [mkC, hbf.2.2 h]
    · exact Local_CC_int (h6 c' h).1 (h6 c' h).2.1
  -- no ghost edge
  have hNG : Γ's.NoGhost := by
    intro c' hc'
    rcases memΓ' c' hc' with h | h | h | h
    · obtain ⟨c, hc, rfl⟩ := Local_mem_liftCs.1 h
      exact hG c (memΓ c (by simp [hc]))
    · exact (Local_isRandom_kinds (hD'r c' h)).2.2.2.2
    · exact (Local_isRandom_kinds (hP'r c' h)).2.2.2.2
    · exact (h6 c' h).2.2.2.2.1
  -- the clause on the external atoms
  obtain ⟨E1, E2, E3, E4, E5⟩ := hE
  have inK' : ∀ c' ∈ Γ's.comps, c'.kind.isRandom = false → c' ∈ liftCs j K ∨ c' ∈ N := by
    intro c' hc' hr
    rcases memΓ' c' hc' with h | h | h | h
    · exact Or.inl h
    · exact absurd (hD'r c' h) (by rw [hr]; simp)
    · exact absurd (hP'r c' h) (by rw [hr]; simp)
    · exact Or.inr h
  have diffK : ∀ c' ∈ Γ's.comps, c'.kind.isDiffusive = true → ∃ c ∈ K, c' = c.map (liftA j) := by
    intro c' hc' hd
    have hr : c'.kind.isRandom = false := Local_diff_notRandom hd
    rcases inK' c' hc' hr with h | h
    · exact Local_mem_liftCs.1 h
    · exact absurd hd (by rw [(h6 c' h).2.2.2.2.2.1]; simp)
  have hdp : ∀ a : Fin 3, Γs.HasDiffToPinned (.inl a) → Γ's.HasDiffToPinned (.inl a) := by
    rintro a ⟨c, hc, hd, hor⟩
    have hcK : c ∈ K := inK c hc (Local_diff_notRandom hd)
    refine ⟨c.map (liftA j), liftmem c hcK, hd, ?_⟩
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by simp [Comp.map, h1, liftA], by
        change ¬ Γ's.Unpinned (liftA j c.y); rw [unpL]; exact h2⟩
    · exact Or.inr ⟨by simp [Comp.map, h1, liftA], by
        change ¬ Γ's.Unpinned (liftA j c.x); rw [unpL]; exact h2⟩
  have hdt : ∀ a : Fin 3, Γs.DiffToPinned (.inl a) → Γ's.DiffToPinned (.inl a) := by
    intro a h c' hc' hd
    obtain ⟨c, hcK, rfl⟩ := diffK c' hc' hd
    obtain ⟨h1, h2⟩ := h c (memΓ c (by simp [hcK])) hd
    refine ⟨fun hx => ?_, fun hy => ?_⟩
    · change ¬ Γ's.Unpinned (liftA j c.y)
      rw [unpL]
      exact h1 ((inl_iff c.x a).1 hx)
    · change ¬ Γ's.Unpinned (liftA j c.x)
      rw [unpL]
      exact h2 ((inl_iff c.y a).1 hy)
  -- the counts of components at an unpinned external atom
  have deg_le : ∀ a : Fin 3, Γs.Unpinned (.inl a) →
      Γ's.nonDotDeg (.inl a) ≤ Γs.nonDotDeg (.inl a) := by
    intro a hU
    let q : Comp (Atom 3 n) → Bool := fun c =>
      decide ((c.x = .inl a ∨ c.y = .inl a) ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)
    let q' : Comp (Atom 3 (n + j)) → Bool := fun c =>
      decide ((c.x = .inl a ∨ c.y = .inl a) ∧ c.kind ≠ .dot ∧ c.kind ≠ .xdot)
    have hfx : ∀ c ∈ Γs.comps, c.kind.isRandom = true → c.x ≠ .inl a := by
      intro c hc hr hx
      have := ((hCC c hc).1 hr).1
      rw [hx, Local_flat_unpinned hU] at this
      simp at this
    have e0 : Γ's.nonDotDeg (.inl a) = Γ's.comps.countP q' := by
      unfold Graph.nonDotDeg
      rw [List.countP_eq_length_filter]
    have e1 : Γs.nonDotDeg (.inl a) = Γs.comps.countP q := by
      unfold Graph.nonDotDeg
      rw [List.countP_eq_length_filter]
    rw [e0, e1, ← hc2.countP_eq, hc1.countP_eq]
    simp only [List.countP_append]
    have cK : (liftCs j K).countP q' = K.countP q := by
      unfold liftCs
      rw [List.countP_map]
      congr 1
      funext c
      simp only [Function.comp_apply, q, q', Comp.map, inl_iff]
    have cD : D'.countP q' ≤ D.countP q := by
      refine Local_countP_f2 h3 fun d d' hm hq => ?_
      obtain ⟨hk, hr, hx, hy, -⟩ := hm
      simp only [q, q', decide_eq_true_eq] at hq ⊢
      refine ⟨?_, (Local_isRandom_kinds hr).1, (Local_isRandom_kinds hr).2.1⟩
      rcases hq.1 with h | h
      · left
        rcases hx with hx | ⟨-, hx⟩
        · exact (inl_iff _ _).1 (hx ▸ h)
        · rw [h] at hx; simp at hx
      · right
        rcases hy with hy | ⟨-, hy⟩
        · exact (inl_iff _ _).1 (hy ▸ h)
        · rw [h] at hy; simp at hy
    have cP : P'.countP q' ≤ P.countP q := by
      rcases h4 with ⟨rfl, rfl⟩ | ⟨c, ch, u, v, rfl, hk, hu, hv, -, -, hp⟩
      · simp
      · rw [hp.countP_eq]
        have hcr : c.kind.isRandom = true := by rcases hk with hk | hk | hk <;> rw [hk] <;> rfl
        have hcx := hfx c (memΓ c (by simp)) hcr
        have h1 : q' (solidC ch (liftA j c.x) u) = false := by
          unfold solidC
          split_ifs with he
          · subst he
            simp only [q', mkC, decide_eq_false_iff_not]
            rintro ⟨h | h, -⟩ <;> rw [h] at hu <;> simp at hu
          · simp only [q', mkC, decide_eq_false_iff_not]
            rintro ⟨h | h, -⟩
            · exact hcx ((inl_iff _ _).1 h)
            · rw [h] at hu; simp at hu
        set b := (if c.kind.isWeight then c.x else c.y) with hbdef
        have h2 : q' (solidC ch v (liftA j b)) = true → q c = true := by
          intro h
          unfold solidC at h
          split_ifs at h with he
          · simp only [q', mkC, decide_eq_true_eq] at h
            rcases h.1 with h' | h' <;> rw [h'] at hv <;> simp at hv
          · simp only [q', mkC, decide_eq_true_eq] at h
            rcases h.1 with h' | h'
            · rw [h'] at hv; simp at hv
            · have hb := (inl_iff _ _).1 h'
              have hk' := Local_isRandom_kinds hcr
              simp only [q, decide_eq_true_eq]
              refine ⟨?_, hk'.1, hk'.2.1⟩
              by_cases hw : c.kind.isWeight = true
              · rw [hbdef, if_pos hw] at hb
                exact absurd hb hcx
              · rw [hbdef, if_neg hw] at hb
                exact Or.inr hb
        simp only [List.countP_cons, List.countP_nil, h1]
        by_cases hq : q' (solidC ch v (liftA j b)) = true
        · simp [hq, h2 hq]
        · simp [hq]
    have cN : N.countP q' = 0 := by
      rw [List.countP_eq_zero]
      intro c hc
      simp only [q', decide_eq_true_eq, not_and]
      intro h
      rcases h with h | h
      · have := (h6 c hc).1; rw [h] at this; simp at this
      · have := (h6 c hc).2.1; rw [h] at this; simp at this
    rw [cK, cN]
    omega
  have hExt : Γ's.ExtClause := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro u' v' hne hb
      rcases Local_atom_cases j u' with ⟨u, rfl⟩ | ⟨i, rfl⟩
      · rcases Local_atom_cases j v' with ⟨v, rfl⟩ | ⟨i, rfl⟩
        · obtain ⟨b, hb'⟩ := E1 u v (fun h => hne (by rw [h]))
            ((Local_lift_sameBlock hL u v).1 hb)
          exact ⟨Fin.castAdd j b, (Local_lift_sameBlock hL u (.inr b)).2 hb'⟩
        · exact absurd (Local_new_block hL i hb.symm) (Local_lift_ne_new j u i)
      · exact absurd (Local_new_block hL i hb).symm hne
    · intro c' hc' hk
      have hr : c'.kind.isRandom = false := by rw [hk]; rfl
      rcases inK' c' hc' hr with h | h
      · obtain ⟨c, hcK, rfl⟩ := Local_mem_liftCs.1 h
        rintro ⟨h1, h2⟩
        exact E2 c (memΓ c (by simp [hcK])) hk ⟨(unpL c.x).1 h1, (unpL c.y).1 h2⟩
      · exact absurd hk (h6 c' h).2.2.2.1
    · intro hU
      have hU' := (unpL (.inl 0)).1 hU
      obtain ⟨a1, a2⟩ := E3 hU'
      exact ⟨hdp 0 a1, hdt 0 a2⟩
    · intro hU
      have hU' := (unpL (.inl 2)).1 hU
      obtain ⟨a1, a2⟩ := E4 hU'
      refine ⟨fun c' hc' hd => ?_, le_trans (deg_le 2 hU') a2⟩
      obtain ⟨c, hcK, rfl⟩ := diffK c' hc' hd
      obtain ⟨b1, b2⟩ := a1 c (memΓ c (by simp [hcK])) hd
      exact ⟨fun h => b1 ((inl_iff _ _).1 h), fun h => b2 ((inl_iff _ _).1 h)⟩
    · intro hU
      have hU' := (unpL (.inl 1)).1 hU
      obtain ⟨a1, a2, a3⟩ := E5 hU'
      refine ⟨?_, hdt 1 a2, le_trans (deg_le 1 hU') a3⟩
      rcases a1 with ⟨c, hc, hk, hor⟩ | h
      · left
        have hcr : c.kind.isRandom = true := by rw [hk]; rfl
        have hcx : c.x ≠ .inl 1 := by
          intro hx
          have := ((hCC c hc).1 hcr).1
          rw [hx, Local_flat_unpinned hU'] at this
          simp at this
        have hcy : c.y = .inl 1 := hor.resolve_left hcx
        have := hc1.mem_iff.1 hc
        simp only [List.mem_append] at this
        rcases this with ((h | h) | h) | h
        · exact ⟨c.map (liftA j), liftmem c h, hk, Or.inr (by simp [Comp.map, hcy, liftA])⟩
        · obtain ⟨d', hd', hm⟩ := Local_f2_left h3 h
          refine ⟨d', hc2.mem_iff.1 (by simp [hd']), by
            rcases hm.1 with h' | ⟨hw, -⟩
            · rw [h', hk]
            · rw [hk] at hw; simp [Kind.isWeight] at hw, Or.inr ?_⟩
          rcases hm.2.2.2.1 with hy | ⟨hy, -⟩
          · rw [hy, hcy]; rfl
          · rw [hcy] at hy; simp at hy
        · rcases h4 with ⟨rfl, -⟩ | ⟨c₀, ch, u, v, rfl, hk₀, hu, hv, -, -, hp⟩
          · simp at h
          · simp only [List.mem_singleton] at h
            subst h
            have hch : ch = .plus := by
              rcases hk₀ with h' | h' | h' <;> rw [hk] at h' <;> simp at h'
              exact h'.symm
            subst hch
            have hw : c.kind.isWeight = false := by rw [hk]; rfl
            refine ⟨solidC .plus v (liftA j (if c.kind.isWeight then c.x else c.y)),
              hc2.mem_iff.1 (by simp [hp.mem_iff]), ?_, Or.inr ?_⟩
            · simp only [hw, Bool.false_eq_true, ↓reduceIte, hcy]
              unfold solidC
              rw [if_neg (fun h => by rw [h] at hv; simp [liftA] at hv)]
              rfl
            · simp only [hw, Bool.false_eq_true, ↓reduceIte, hcy]
              unfold solidC
              rw [if_neg (fun h => by rw [h] at hv; simp [liftA] at hv)]
              rfl
        · exact absurd (h5 c h) (by rw [hk]; simp [Kind.isWeight])
      · exact Or.inr (hdp 1 h)
  exact ⟨hColour, hExt, hNG⟩

/-- A term of `Local_Dec`: its molecular graph is carried from that of the graph along `liftA j`,
and it keeps the charge pattern of the block normal form, the clause on the external atoms and the
absence of ghost edges. -/
private theorem Local_dec_main {Γ : Graph 3 n} {x : Fin n} {j : ℕ} {Γ' : Graph 3 (n + j)}
    (hd : Local_Dec Γ x j Γ') (hC : Γ.ColourInvB) (hE : Γ.ExtClause) (hG : Γ.NoGhost) :
    Local_Carry Γ.toMG' Γ'.toMG' (liftA j) ∧ Γ'.ColourInvB ∧ Γ'.ExtClause ∧ Γ'.NoGhost := by
  refine ⟨Local_dec_carry hd hC, ?_⟩
  obtain ⟨K, D, P, R, D', P', N, h1, h2, h3, h4, h5, h6, h7⟩ := hd
  have hL := Local_dec_liftOK h1 h2 h3 h4 h5 h6 h7
  have e := Local_same3_clauses (Local_strip_same3 Γ)
  have e' := Local_same3_clauses (Local_strip_same3 Γ')
  obtain ⟨a1, a2, a3⟩ := Local_dec_clauses_strip h1 h2 h3 h4 h5 h6 hL (e.1.2 hC) (e.2.1.2 hE)
    (e.2.2.2 hG)
  exact ⟨e'.1.1 a1, e'.2.1.1 a2, e'.2.2.1 a3⟩

/-- The representatives of the molecules of the term at the original atoms and at the new atoms. -/
private theorem Local_dec_molRep {Γ : Graph 3 n} {x : Fin n} {j : ℕ} {Γ' : Graph 3 (n + j)}
    (hd : Local_Dec Γ x j Γ') (u : Atom 3 (n + j)) :
    Γ'.molRep u = liftA j (Γ.molRep (Local_proj j x u)) := by
  obtain ⟨K, D, P, R, D', P', N, h1, h2, h3, h4, h5, h6, h7⟩ := hd
  have hL := Local_dec_liftOK h1 h2 h3 h4 h5 h6 h7
  have e := (Local_same3_fun (Local_strip_same3 Γ)).2.2.2.1
  have e' := (Local_same3_fun (Local_strip_same3 Γ')).2.2.2.1
  rw [← e', Local_lift_molRep hL, e]

end DecMain

/-! ## The blocks of the dotted edges and `Graph.mergeT` -/

section Blocks

variable {V : Type*} [DecidableEq V]

/-- The relation "joined by a dotted component". -/
private def Local_dotRel (cs : List (Comp V)) : V → V → Prop :=
  fun u v => ∃ c ∈ cs, c.kind = .dot ∧ c.x = u ∧ c.y = v

omit [DecidableEq V] in
private theorem Local_dotRel_mono {cs cs' : List (Comp V)} (h : ∀ c ∈ cs, c ∈ cs') :
    Local_dotRel cs ≤ Local_dotRel cs' := by
  rintro u v ⟨c, hc, hk, hx, hy⟩
  exact ⟨c, h c hc, hk, hx, hy⟩

omit [DecidableEq V] in
private theorem Local_flatten_map_singleton (as : List V) : (as.map fun a => [a]).flatten = as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

private theorem Local_joinBlocks_flatten_perm (P : List (List V)) (u v : V) :
    (joinBlocks P u v).flatten.Perm P.flatten := by
  unfold joinBlocks
  rw [List.flatten_append, List.flatten_singleton]
  have h := (List.filter_append_perm (fun B : List V => B.contains u || B.contains v) P).flatten
  rw [List.flatten_append] at h
  exact List.perm_append_comm.trans h

/-- One step of `dotBlocks`. -/
private def Local_blockStep (c : Comp V) (P : List (List V)) : List (List V) :=
  if c.kind = .dot then joinBlocks P c.x c.y else P

private theorem Local_dotBlocks_snoc (as : List V) (cs : List (Comp V)) (c : Comp V) :
    dotBlocks as (cs ++ [c]) = Local_blockStep c (dotBlocks as cs) := by
  simp [dotBlocks, List.foldl_append, Local_blockStep]

private theorem Local_dotBlocks_nil (as : List V) : dotBlocks as ([] : List (Comp V)) =
    as.map fun a => [a] := rfl

private theorem Local_dotBlocks_flatten_perm (as : List V) (cs : List (Comp V)) :
    (dotBlocks as cs).flatten.Perm as := by
  induction cs using List.reverseRecOn with
  | nil => rw [Local_dotBlocks_nil, Local_flatten_map_singleton]
  | append_singleton cs c ih =>
    rw [Local_dotBlocks_snoc, Local_blockStep]
    split_ifs
    · exact (Local_joinBlocks_flatten_perm _ _ _).trans ih
    · exact ih

private theorem Local_dotBlocks_conn (as : List V) (cs : List (Comp V)) :
    ∀ B ∈ dotBlocks as cs, ∀ u ∈ B, ∀ v ∈ B, Relation.EqvGen (Local_dotRel cs) u v := by
  induction cs using List.reverseRecOn with
  | nil =>
    intro B hB u hu v hv
    rw [Local_dotBlocks_nil, List.mem_map] at hB
    obtain ⟨a, -, rfl⟩ := hB
    simp only [List.mem_singleton] at hu hv
    subst hu; subst hv
    exact Relation.EqvGen.refl _
  | append_singleton cs c ih =>
    have hmono : ∀ u v, Relation.EqvGen (Local_dotRel cs) u v →
        Relation.EqvGen (Local_dotRel (cs ++ [c])) u v := fun u v h =>
      Relation.EqvGen.mono (Local_dotRel_mono fun c' hc' => List.mem_append_left _ hc') u v h
    intro B hB u hu v hv
    rw [Local_dotBlocks_snoc, Local_blockStep] at hB
    split_ifs at hB with hk
    · unfold joinBlocks at hB
      rw [List.mem_append] at hB
      rcases hB with hB | hB
      · exact hmono _ _ (ih B (List.mem_of_mem_filter hB) u hu v hv)
      · rw [List.mem_singleton] at hB
        subst hB
        have hxy : Relation.EqvGen (Local_dotRel (cs ++ [c])) c.x c.y :=
          Relation.EqvGen.rel _ _ ⟨c, List.mem_append_right _ (List.mem_singleton_self _), hk, rfl,
            rfl⟩
        -- every element of the joined block is connected to `c.x` by dotted edges
        have key : ∀ w ∈ (dotBlocks as cs).filter (fun B => B.contains c.x || B.contains c.y),
            ∀ z ∈ w, Relation.EqvGen (Local_dotRel (cs ++ [c])) z c.x := by
          intro w hw z hz
          have hw' := List.mem_filter.1 hw
          have hcont := hw'.2
          simp only [Bool.or_eq_true, List.contains_iff_mem] at hcont
          rcases hcont with hx | hy
          · exact hmono _ _ (ih w hw'.1 z hz _ hx)
          · exact (hmono _ _ (ih w hw'.1 z hz _ hy)).trans _ _ _ hxy.symm
        rw [List.mem_flatten] at hu hv
        obtain ⟨w₁, hw₁, hu⟩ := hu
        obtain ⟨w₂, hw₂, hv⟩ := hv
        exact (key w₁ hw₁ u hu).trans _ _ _ (key w₂ hw₂ v hv).symm
    · exact hmono _ _ (ih B hB u hu v hv)

private theorem Local_dotBlocks_joined (as : List V) (cs : List (Comp V))
    (hcs : ∀ c ∈ cs, c.x ∈ as ∧ c.y ∈ as) :
    ∀ c ∈ cs, c.kind = .dot → ∃ B ∈ dotBlocks as cs, c.x ∈ B ∧ c.y ∈ B := by
  induction cs using List.reverseRecOn with
  | nil => intro c hc; simp at hc
  | append_singleton cs c ih =>
    have ih' := ih fun c' hc' => hcs c' (List.mem_append_left _ hc')
    intro c' hc' hk'
    rw [Local_dotBlocks_snoc, Local_blockStep]
    -- membership of an atom of `as` in some block
    have hmem : ∀ a ∈ as, ∃ B ∈ dotBlocks as cs, a ∈ B := by
      intro a ha
      have := (Local_dotBlocks_flatten_perm as cs).mem_iff.2 ha
      rwa [List.mem_flatten] at this
    split_ifs with hk
    · rcases List.mem_append.1 hc' with hc' | hc'
      · obtain ⟨B, hB, hx, hy⟩ := ih' c' hc' hk'
        by_cases hcB : (B.contains c.x || B.contains c.y) = true
        · refine ⟨(dotBlocks as cs |>.filter fun B => B.contains c.x || B.contains c.y).flatten,
            ?_, ?_, ?_⟩
          · unfold joinBlocks
            exact List.mem_append_right _ (List.mem_singleton_self _)
          · rw [List.mem_flatten]
            exact ⟨B, List.mem_filter.2 ⟨hB, hcB⟩, hx⟩
          · rw [List.mem_flatten]
            exact ⟨B, List.mem_filter.2 ⟨hB, hcB⟩, hy⟩
        · refine ⟨B, ?_, hx, hy⟩
          unfold joinBlocks
          refine List.mem_append_left _ (List.mem_filter.2 ⟨hB, ?_⟩)
          simpa using hcB
      · rw [List.mem_singleton] at hc'
        subst hc'
        obtain ⟨hxa, hya⟩ := hcs _ (List.mem_append_right _ (List.mem_singleton_self _))
        obtain ⟨B₁, hB₁, hx⟩ := hmem _ hxa
        obtain ⟨B₂, hB₂, hy⟩ := hmem _ hya
        refine ⟨(dotBlocks as cs |>.filter fun B => B.contains c'.x || B.contains c'.y).flatten,
          ?_, ?_, ?_⟩
        · unfold joinBlocks
          exact List.mem_append_right _ (List.mem_singleton_self _)
        · rw [List.mem_flatten]
          exact ⟨B₁, List.mem_filter.2 ⟨hB₁, by simp [hx]⟩, hx⟩
        · rw [List.mem_flatten]
          exact ⟨B₂, List.mem_filter.2 ⟨hB₂, by simp [hy]⟩, hy⟩
    · rcases List.mem_append.1 hc' with hc' | hc'
      · exact ih' c' hc' hk'
      · rw [List.mem_singleton] at hc'
        subst hc'
        exact absurd hk' hk

/-- Two atoms of one block of a partition have the same representative. -/
private theorem Local_blockRep_eq_of_mem {P : List (List V)} (hnd : P.flatten.Nodup) {B : List V}
    (hB : B ∈ P) {u v : V} (hu : u ∈ B) (hv : v ∈ B) : blockRep P u = blockRep P v := by
  have hfind : ∀ w ∈ B, P.find? (fun B' => B'.contains w) = some B := by
    intro w hw
    have hex : (P.find? (fun B' => B'.contains w)).isSome = true :=
      List.find?_isSome.2 ⟨B, hB, by simpa [List.contains_iff_mem] using hw⟩
    obtain ⟨B', hB'⟩ := Option.isSome_iff_exists.1 hex
    rw [hB']
    have hB'mem := List.mem_of_find?_eq_some hB'
    have hw' : w ∈ B' := by simpa [List.contains_iff_mem] using List.find?_some hB'
    congr 1
    by_contra hne
    rw [List.nodup_flatten] at hnd
    have := hnd.2.forall (R := List.Disjoint) hB'mem hB hne
    exact this hw' hw
  unfold blockRep
  rw [hfind u hu, hfind v hv]
  cases B with
  | nil => simp at hu
  | cons r rest => rfl

private theorem Local_blockRep_spec (P : List (List V)) (u : V) :
    blockRep P u = u ∨ ∃ B ∈ P, u ∈ B ∧ blockRep P u ∈ B := by
  unfold blockRep
  generalize hf : P.find? (fun B => B.contains u) = o
  rcases o with _ | ⟨_ | ⟨r, rest⟩⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · right
    refine ⟨r :: rest, List.mem_of_find?_eq_some hf, ?_, List.mem_cons_self ..⟩
    simpa [List.contains_iff_mem] using List.find?_some hf

end Blocks

/-! ## The data of `O_merge` -/

section MergeData

variable {k n : ℕ}

private theorem Local_mem_allAtoms (u : Atom k n) : u ∈ allAtoms k n := by
  rcases u with a | i <;> simp [allAtoms]

private theorem Local_allAtoms_nodup : (allAtoms k n).Nodup := by
  unfold allAtoms
  rw [List.nodup_append]
  refine ⟨(List.nodup_finRange k).map Sum.inl_injective,
    (List.nodup_finRange n).map Sum.inr_injective, ?_⟩
  intro a ha b hb hab
  simp only [List.mem_map] at ha hb
  obtain ⟨i, -, rfl⟩ := ha
  obtain ⟨j, -, rfl⟩ := hb
  simp at hab

/-- The representative of an atom in the dot blocks of a graph. -/
private def Local_mrep (Γ : Graph k n) : Atom k n → Atom k n :=
  blockRep (dotBlocks (allAtoms k n) Γ.comps)

private theorem Local_mrep_dot (Γ : Graph k n) {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hk : c.kind = .dot) : (Local_mrep Γ) c.x = (Local_mrep Γ) c.y := by
  obtain ⟨B, hB, hx, hy⟩ := Local_dotBlocks_joined (allAtoms k n) Γ.comps
    (fun c _ => ⟨Local_mem_allAtoms _, Local_mem_allAtoms _⟩) c hc hk
  have hnd : (dotBlocks (allAtoms k n) Γ.comps).flatten.Nodup :=
    (Local_dotBlocks_flatten_perm _ _).nodup_iff.2 Local_allAtoms_nodup
  exact Local_blockRep_eq_of_mem hnd hB hx hy

private theorem Local_mrep_conn (Γ : Graph k n) (u : Atom k n) :
    Relation.EqvGen (Local_dotRel Γ.comps) u ((Local_mrep Γ) u) := by
  rcases Local_blockRep_spec (dotBlocks (allAtoms k n) Γ.comps) u with h | ⟨B, hB, hu, hr⟩
  · have : (Local_mrep Γ) u = u := h
    rw [this]
    exact Relation.EqvGen.refl _
  · exact Local_dotBlocks_conn _ _ B hB u hu _ hr

/-- The roots: the representatives of the internal atoms, without repetition. -/
private def Local_mroots (Γ : Graph k n) : List (Atom k n) :=
  ((List.finRange n).map fun i => (Local_mrep Γ) (Sum.inr i)).dedup

private theorem Local_mem_mroots (Γ : Graph k n) (i : Fin n) : (Local_mrep Γ) (.inr i) ∈ (Local_mroots Γ) :=
  List.mem_dedup.2 (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)

/-- The new internal atom of an internal atom: the position of its root. -/
private def Local_midx (Γ : Graph k n) (i : Fin n) : Fin (Local_mroots Γ).length :=
  ⟨(Local_mroots Γ).idxOf ((Local_mrep Γ) (.inr i)), List.idxOf_lt_length_of_mem (Local_mem_mroots Γ i)⟩

/-- The atom map of `O_merge`. -/
private def Local_mmap (Γ : Graph k n) : Atom k n → Atom k (Local_mroots Γ).length :=
  fun u => match u with
    | .inl a => .inl a
    | .inr i => .inr ((Local_midx Γ) i)

/-- The image of a component under `O_merge`, or `none` if it is removed. -/
private def Local_mergeComp {m : ℕ} (rep : Atom k n → Atom k n) (f : Atom k n → Atom k m)
    (c : Comp (Atom k n)) : Option (Comp (Atom k m)) :=
  if c.kind == .dot && f c.x == f c.y then none
  else if c.kind.isSolid && rep c.x == rep c.y then
    some { c.map f with kind := c.kind.toWeight, y := f c.x }
  else some (c.map f)

private theorem Local_mergeT_eq (Γ : Graph k n) : Γ.mergeT =
    if Γ.comps.any (fun c => c.kind == .xdot && (Local_mrep Γ) c.x == (Local_mrep Γ) c.y) then none else
    some ⟨(Local_mroots Γ).length, ⟨Γ.comps.filterMap (Local_mergeComp (Local_mrep Γ) (Local_mmap Γ)), Γ.coeff⟩, (Local_mmap Γ)⟩ := rfl

/-- The structure of a tracked graph `t` with `Γ.mergeT = some t`: its components, its atom map
and its blocks. -/
private structure Local_MergeSpec (Γ : Graph k n) (t : Tracked k n) : Prop where
  comps_eq : t.g.comps = Γ.comps.filterMap (Local_mergeComp (Local_mrep Γ) t.f)
  coeff_eq : t.g.coeff = Γ.coeff
  nOut_le : t.nOut ≤ n
  f_inl : ∀ a, t.f (.inl a) = .inl a
  f_surj : Function.Surjective t.f
  f_inr : ∃ g : Fin n → Fin t.nOut, (∀ i, t.f (.inr i) = .inr (g i)) ∧ Function.Surjective g
  f_eq : ∀ u v, (Local_mrep Γ) u = (Local_mrep Γ) v → u.isRight = true → v.isRight = true → t.f u = t.f v
  f_ne : ∀ u v, (Local_mrep Γ) u ≠ (Local_mrep Γ) v → t.f u ≠ t.f v
  xdot_ne : ∀ c ∈ Γ.comps, c.kind = .xdot → (Local_mrep Γ) c.x ≠ (Local_mrep Γ) c.y

private theorem Local_mergeT_none {Γ : Graph k n} (h : Γ.mergeT = none) :
    ∃ c ∈ Γ.comps, c.kind = .xdot ∧ (Local_mrep Γ) c.x = (Local_mrep Γ) c.y := by
  rw [Local_mergeT_eq] at h
  split_ifs at h with hc
  rw [List.any_eq_true] at hc
  obtain ⟨c, hc, hb⟩ := hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  exact ⟨c, hc, hb.1, hb.2⟩

private theorem Local_mergeT_spec {Γ : Graph k n} {t : Tracked k n} (h : Γ.mergeT = some t) :
    Local_MergeSpec Γ t := by
  rw [Local_mergeT_eq] at h
  split_ifs at h with hc
  obtain rfl := Option.some.inj h
  have hsurj : Function.Surjective (Local_midx Γ) := by
    intro j
    have hj : (Local_mroots Γ)[j.1] ∈ (Local_mroots Γ) := List.getElem_mem j.2
    obtain ⟨i, -, hi⟩ := List.mem_map.1 (List.mem_dedup.1 hj)
    refine ⟨i, Fin.ext ?_⟩
    simp only [Local_midx]
    rw [hi]
    exact (List.nodup_dedup _).idxOf_getElem j.1 j.2
  refine ⟨rfl, rfl, ?_, fun a => rfl, ?_, ⟨(Local_midx Γ), fun i => rfl, hsurj⟩, ?_, ?_, ?_⟩
  · exact (List.dedup_sublist _).length_le.trans (by simp)
  · intro u'
    rcases u' with a | j
    · exact ⟨.inl a, rfl⟩
    · obtain ⟨i, hi⟩ := hsurj j
      exact ⟨.inr i, by simp [Local_mmap, hi]⟩
  · intro u v huv hu hv
    rcases u with a | i
    · simp at hu
    rcases v with b | j
    · simp at hv
    have : (Local_midx Γ) i = (Local_midx Γ) j := Fin.ext (by
      change (Local_mroots Γ).idxOf ((Local_mrep Γ) (.inr i)) = (Local_mroots Γ).idxOf ((Local_mrep Γ) (.inr j))
      rw [huv])
    simp [Local_mmap, this]
  · intro u v huv hf
    rcases u with a | i <;> rcases v with b | j
    · simp only [Local_mmap, Sum.inl.injEq] at hf
      exact huv (by rw [hf])
    · simp [Local_mmap] at hf
    · simp [Local_mmap] at hf
    · simp only [Local_mmap, Sum.inr.injEq] at hf
      have h2 := congrArg Fin.val hf
      simp only [Local_midx] at h2
      exact huv ((List.idxOf_inj (Local_mem_mroots Γ i)).1 h2)
  · intro c hcm hk hcc
    apply hc
    rw [List.any_eq_true]
    exact ⟨c, hcm, by simp [hk, hcc]⟩

end MergeData

/-! ## The molecular graph after `O_merge` -/

section MergeRead

variable {k n : ℕ}

private theorem Local_sameBlock_of_eqv {Γ : Graph k n} {u v : Atom k n}
    (h : Relation.EqvGen (Local_dotRel Γ.comps) u v) : Γ.SameBlock u v := by
  induction h with
  | rel x y hxy =>
    obtain ⟨c, hc, hk, rfl, rfl⟩ := hxy
    by_cases he : c.x = c.y
    · rw [he]
      exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (by
        simp only [Graph.dotGraph, SimpleGraph.fromRel_adj]
        exact ⟨he, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩)
  | refl x => exact SimpleGraph.Reachable.refl _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- The representatives of `O_merge` are those of the blocks. -/
private theorem Local_mrep_iff (Γ : Graph k n) (u v : Atom k n) :
    Local_mrep Γ u = Local_mrep Γ v ↔ Γ.SameBlock u v := by
  constructor
  · intro h
    have h1 := Local_sameBlock_of_eqv (Local_mrep_conn Γ u)
    have h2 := Local_sameBlock_of_eqv (Local_mrep_conn Γ v)
    rw [h] at h1
    exact h1.trans h2.symm
  · intro h
    obtain ⟨w⟩ := h
    induction w with
    | nil => rfl
    | cons hab _ ih =>
      rw [← ih]
      simp only [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab
      rcases hab.2 with ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩
      · exact Local_mrep_dot Γ hc hk
      · exact (Local_mrep_dot Γ hc hk).symm

private theorem Local_solid_kinds {κ : Kind} (h : κ.isSolid = true) :
    κ ≠ .dot ∧ κ ≠ .xdot ∧ κ.isRandom = true ∧ κ.joinsMol = false := by
  cases κ <;> simp_all [Kind.isSolid, Kind.isRandom, Kind.joinsMol]

private theorem Local_toWeight_solid {κ : Kind} (h : κ.isSolid = true) :
    κ.toWeight ≠ .dot ∧ κ.toWeight.joinsMol = false ∧ κ.toWeight.isRandom = true ∧
      κ.toWeight.mclass = none ∧ κ.toWeight ≠ .xdot ∧ κ.toWeight ≠ .ghost ∧
      κ.toWeight.isDiffusive = false ∧ κ.toWeight.isWeight = true := by
  cases κ <;> simp_all [Kind.isSolid, Kind.toWeight, Kind.joinsMol, Kind.isRandom, Kind.mclass,
    Kind.isDiffusive, Kind.isWeight]

private theorem Local_mergeComp_none {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} (h : Local_mergeComp rep f c = none) : c.kind = .dot ∧ f c.x = f c.y := by
  unfold Local_mergeComp at h
  split_ifs at h with h1
  simpa using h1

private theorem Local_mergeComp_some {m : ℕ} {rep : Atom k n → Atom k n} {f : Atom k n → Atom k m}
    {c : Comp (Atom k n)} {c' : Comp (Atom k m)} (h : Local_mergeComp rep f c = some c') :
    (c.kind.isSolid = true ∧ rep c.x = rep c.y ∧
      c' = { (c.map f) with kind := c.kind.toWeight, y := f c.x }) ∨
      (c' = c.map f ∧ ¬ (c.kind = .dot ∧ f c.x = f c.y) ∧
        ¬ (c.kind.isSolid = true ∧ rep c.x = rep c.y)) := by
  unfold Local_mergeComp at h
  split_ifs at h with h1 h2
  · obtain rfl := Option.some.inj h
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact Or.inl ⟨h2.1, h2.2, rfl⟩
  · obtain rfl := Option.some.inj h
    exact Or.inr ⟨rfl, by simpa using h1, by simpa using h2⟩

/-- Pulling back reachability along a surjective map whose fibres are reachable. -/
private theorem Local_reach_pull {W W' : Type} {Gr : SimpleGraph W} {Gr' : SimpleGraph W'}
    (f : W → W') (hfib : ∀ a b, f a = f b → Gr.Reachable a b)
    (hadj : ∀ a' b', Gr'.Adj a' b' → ∃ a b, f a = a' ∧ f b = b' ∧ Gr.Reachable a b)
    {u v : W} (hr : Gr'.Reachable (f u) (f v)) : Gr.Reachable u v := by
  suffices key : ∀ u' v' (p : Gr'.Walk u' v') (u v : W), f u = u' → f v = v' → Gr.Reachable u v from
    hr.elim fun p => key _ _ p u v rfl rfl
  intro u' v' p
  induction p with
  | nil => intro u v hu hv; exact hfib u v (hu.trans hv.symm)
  | cons hadj' _ ih =>
    intro u v hu hv
    obtain ⟨a, b, ha, hb, hab⟩ := hadj _ _ hadj'
    exact (hfib u a (hu.trans ha.symm)).trans (hab.trans (ih b v hb hv))

/-- Atoms of one block are read at the same molecule, on a graph whose blocks with two or more
atoms contain an internal atom. -/
private theorem Local_rho_block {Γ : Graph k n} {u v : Atom k n} (huv : Γ.SameBlock u v)
    (hb : ∃ b : Fin n, Γ.SameBlock u (.inr b)) : Local_rho Γ u = Local_rho Γ v := by
  obtain ⟨b, hb⟩ := hb
  unfold Local_rho
  rw [Local_molRep_flat hb, Local_molRep_flat (huv.symm.trans hb)]

section Spec

variable {G : Graph k n} {t : Tracked k n} (h : G.mergeT = some t)
include h

private theorem Local_merge_fiber {a b : Atom k n} (hab : t.f a = t.f b) : G.SameBlock a b := by
  have hs := Local_mergeT_spec h
  by_contra hn
  exact hs.f_ne a b (fun h' => hn ((Local_mrep_iff G a b).1 h')) hab

private theorem Local_merge_f_int {u : Atom k n} : (t.f u).isRight = u.isRight := by
  have hs := Local_mergeT_spec h
  cases u with
  | inl a => rw [hs.f_inl a]; rfl
  | inr i =>
    obtain ⟨g, hg, -⟩ := hs.f_inr
    rw [hg i]; rfl

private theorem Local_merge_comps : t.g.comps = G.comps.filterMap (Local_mergeComp (Local_mrep G) t.f) :=
  (Local_mergeT_spec h).comps_eq

/-- A component of the graph of `Graph.mergeT` and the component of `G` it comes from. -/
private theorem Local_merge_mem {c' : Comp (Atom k t.nOut)} (hc' : c' ∈ t.g.comps) :
    ∃ c ∈ G.comps, Local_mergeComp (Local_mrep G) t.f c = some c' := by
  rw [Local_merge_comps h] at hc'
  exact List.mem_filterMap.1 hc'

private theorem Local_merge_sameBlock (u v : Atom k n) :
    t.g.SameBlock (t.f u) (t.f v) ↔ G.SameBlock u v := by
  constructor
  · intro hr
    refine Local_reach_pull t.f (fun a b hab => Local_merge_fiber h hab) (fun a' b' hab => ?_) hr
    simp only [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab
    have key : ∀ a' b', (∃ c ∈ t.g.comps, c.kind = .dot ∧ c.x = a' ∧ c.y = b') →
        ∃ a b, t.f a = a' ∧ t.f b = b' ∧ G.dotGraph.Reachable a b := by
      rintro a' b' ⟨c', hc', hk, rfl, rfl⟩
      obtain ⟨c, hc, hm⟩ := Local_merge_mem h hc'
      rcases Local_mergeComp_some hm with ⟨hsol, -, rfl⟩ | ⟨rfl, -, -⟩
      · exact absurd hk (Local_toWeight_solid hsol).1
      · refine ⟨c.x, c.y, rfl, rfl, ?_⟩
        by_cases hxy : c.x = c.y
        · rw [hxy]
        · exact SimpleGraph.Adj.reachable (by
            simp only [Graph.dotGraph, SimpleGraph.fromRel_adj]
            exact ⟨hxy, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩)
    rcases hab.2 with hab' | hab'
    · exact key a' b' hab'
    · obtain ⟨a, b, ha, hb, hr⟩ := key b' a' hab'
      exact ⟨b, a, hb, ha, hr.symm⟩
  · intro hr
    refine Local_reach_map t.f (fun a b hab => ?_) hr
    simp only [Graph.dotGraph, SimpleGraph.fromRel_adj] at hab
    have key : ∀ a b, (∃ c ∈ G.comps, c.kind = .dot ∧ c.x = a ∧ c.y = b) →
        t.g.dotGraph.Reachable (t.f a) (t.f b) := by
      rintro a b ⟨c, hc, hk, rfl, rfl⟩
      by_cases he : t.f c.x = t.f c.y
      · rw [he]
      · have hm : Local_mergeComp (Local_mrep G) t.f c = some (c.map t.f) := by
          unfold Local_mergeComp
          rw [if_neg (by simp [he]), if_neg (by simp [hk, Kind.isSolid])]
        have hc' : c.map t.f ∈ t.g.comps := by
          rw [Local_merge_comps h]
          exact List.mem_filterMap.2 ⟨c, hc, hm⟩
        exact SimpleGraph.Adj.reachable (by
          simp only [Graph.dotGraph, SimpleGraph.fromRel_adj]
          exact ⟨he, Or.inl ⟨_, hc', hk, rfl, rfl⟩⟩)
    rcases hab.2 with hab' | hab'
    · exact key a b hab'
    · exact (key b a hab').symm

private theorem Local_merge_molReach (u v : Atom k n) :
    t.g.molGraph.Reachable (t.f u) (t.f v) ↔ G.molGraph.Reachable u v := by
  constructor
  · intro hr
    refine Local_reach_pull t.f (fun a b hab => (Local_merge_fiber h hab).mono
      (Local_dot_le_mol G)) (fun a' b' hab => ?_) hr
    simp only [Graph.molGraph, SimpleGraph.fromRel_adj] at hab
    have key : ∀ a' b', (∃ c ∈ t.g.comps, c.kind.joinsMol = true ∧ c.x = a' ∧ c.y = b') →
        ∃ a b, t.f a = a' ∧ t.f b = b' ∧ G.molGraph.Reachable a b := by
      rintro a' b' ⟨c', hc', hk, rfl, rfl⟩
      obtain ⟨c, hc, hm⟩ := Local_merge_mem h hc'
      rcases Local_mergeComp_some hm with ⟨hsol, -, rfl⟩ | ⟨rfl, -, -⟩
      · exact absurd hk (by rw [(Local_toWeight_solid hsol).2.1]; simp)
      · refine ⟨c.x, c.y, rfl, rfl, ?_⟩
        by_cases hxy : c.x = c.y
        · rw [hxy]
        · exact SimpleGraph.Adj.reachable (by
            simp only [Graph.molGraph, SimpleGraph.fromRel_adj]
            exact ⟨hxy, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩)
    rcases hab.2 with hab' | hab'
    · exact key a' b' hab'
    · obtain ⟨a, b, ha, hb, hr⟩ := key b' a' hab'
      exact ⟨b, a, hb, ha, hr.symm⟩
  · intro hr
    refine Local_reach_map t.f (fun a b hab => ?_) hr
    simp only [Graph.molGraph, SimpleGraph.fromRel_adj] at hab
    have key : ∀ a b, (∃ c ∈ G.comps, c.kind.joinsMol = true ∧ c.x = a ∧ c.y = b) →
        t.g.molGraph.Reachable (t.f a) (t.f b) := by
      rintro a b ⟨c, hc, hk, rfl, rfl⟩
      by_cases he : t.f c.x = t.f c.y
      · rw [he]
      · have hns : c.kind.isSolid = false := by
          cases hck : c.kind <;> simp_all [Kind.joinsMol, Kind.isSolid]
        have hm : Local_mergeComp (Local_mrep G) t.f c = some (c.map t.f) := by
          unfold Local_mergeComp
          rw [if_neg (by simp [he]), if_neg (by simp [hns])]
        have hc' : c.map t.f ∈ t.g.comps := by
          rw [Local_merge_comps h]
          exact List.mem_filterMap.2 ⟨c, hc, hm⟩
        exact SimpleGraph.Adj.reachable (by
          simp only [Graph.molGraph, SimpleGraph.fromRel_adj]
          exact ⟨he, Or.inl ⟨_, hc', hk, rfl, rfl⟩⟩)
    rcases hab.2 with hab' | hab'
    · exact key a b hab'
    · exact (key b a hab').symm

private theorem Local_merge_sameMol (u v : Atom k n) :
    t.g.SameMol (t.f u) (t.f v) ↔ G.SameMol u v := by
  have hfe : ∀ a b, t.f a = t.f b ↔ (a = b ∨ (a.isRight = true ∧ b.isRight = true ∧
      G.SameBlock a b)) := by
    intro a b
    have hs := Local_mergeT_spec h
    constructor
    · intro hab
      by_cases ha : a.isRight = true
      · have hb : b.isRight = true := by
          rw [← Local_merge_f_int h, ← hab, Local_merge_f_int h]; exact ha
        exact Or.inr ⟨ha, hb, Local_merge_fiber h hab⟩
      · left
        cases a with
        | inr i => simp at ha
        | inl a' =>
          cases b with
          | inl b' =>
            simp only [hs.f_inl, Sum.inl.injEq] at hab
            rw [hab]
          | inr j =>
            exfalso
            have := Local_merge_f_int h (u := .inr j)
            rw [← hab, hs.f_inl] at this
            simp at this
    · rintro (rfl | ⟨ha, hb, hab⟩)
      · rfl
      · exact hs.f_eq a b ((Local_mrep_iff G a b).2 hab) ha hb
  constructor
  · rintro (he | ⟨h1, h2, hr⟩)
    · rcases (hfe u v).1 he with rfl | ⟨ha, hb, hab⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨ha, hb, hab.mono (Local_dot_le_mol G)⟩
    · rw [Local_merge_f_int h] at h1 h2
      exact Or.inr ⟨h1, h2, (Local_merge_molReach h u v).1 hr⟩
  · rintro (rfl | ⟨h1, h2, hr⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨?_, ?_, (Local_merge_molReach h u v).2 hr⟩
      · rw [Local_merge_f_int h]; exact h1
      · rw [Local_merge_f_int h]; exact h2

private theorem Local_merge_unpinned (u : Atom k n) : t.g.Unpinned (t.f u) ↔ G.Unpinned u := by
  have hs := Local_mergeT_spec h
  obtain ⟨g, hg, hgs⟩ := hs.f_inr
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun b hb => h2 (g b) ?_⟩
    · cases u with
      | inl a => rfl
      | inr i => rw [hg] at h1; simp at h1
    · rw [← hg]
      exact (Local_merge_sameBlock h u (.inr b)).2 hb
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun b' hb => ?_⟩
    · cases u with
      | inl a => rw [hs.f_inl]; rfl
      | inr i => simp at h1
    · obtain ⟨b, rfl⟩ := hgs b'
      rw [← hg] at hb
      exact h2 b ((Local_merge_sameBlock h u (.inr b)).1 hb)

private theorem Local_merge_f_inl (a : Fin k) : t.f (.inl a) = .inl a := (Local_mergeT_spec h).f_inl a

private theorem Local_merge_molRep (u : Atom k n) :
    t.g.molRep (t.f (G.molRep u)) = t.g.molRep (t.f u) :=
  (Local_molRep_eq_iff _ _ _).2 ((Local_merge_sameMol h _ _).2
    (G.sameMol_equivalence.symm (Local_molRep_spec G u)))

private theorem Local_merge_int (u : Atom k n) (hu : u.isRight = true) :
    ∃ c, t.f u = .inr c := by
  have := Local_merge_f_int h (u := u)
  rw [hu] at this
  cases hf : t.f u with
  | inl a => rw [hf] at this; simp at this
  | inr c => exact ⟨c, rfl⟩

private theorem Local_merge_rho (u : Atom k n) :
    Local_rho t.g (t.f u) = t.g.molRep (t.f (Local_rho G u)) := by
  unfold Local_rho
  cases u with
  | inr i =>
    obtain ⟨c, hc⟩ := Local_merge_int h (.inr i) rfl
    have e1 : t.g.flatAtom (t.f (.inr i)) = t.f (.inr i) := by rw [hc]; rfl
    have e2 : G.flatAtom (.inr i) = .inr i := rfl
    rw [e1, e2, Local_merge_molRep h]
  | inl a =>
    rw [Local_merge_f_inl h a]
    by_cases hU : G.Unpinned (.inl a)
    · have hU' : t.g.Unpinned (.inl a) := by
        rw [← Local_merge_f_inl h a]
        exact (Local_merge_unpinned h _).2 hU
      rw [Local_flat_unpinned hU, Local_flat_unpinned hU']
      show t.g.molRep (.inl a) = t.g.molRep (t.f (.inl a))
      rw [Local_merge_f_inl h a]
    · obtain ⟨b, hb⟩ : ∃ b, G.SameBlock (.inl a) (.inr b) := by
        by_contra hn
        push Not at hn
        exact hU ⟨rfl, hn⟩
      obtain ⟨c, hc⟩ := Local_merge_int h (.inr b) rfl
      have hb' : t.g.SameBlock (.inl a) (.inr c) := by
        rw [← Local_merge_f_inl h a, ← hc]
        exact (Local_merge_sameBlock h _ _).2 hb
      rw [Local_molRep_flat hb', Local_molRep_flat hb, ← hc, Local_merge_molRep h]

/-- The vertices of the molecular graph of `G` are mapped injectively to those of the graph of
`Graph.mergeT`. -/
private theorem Local_merge_injOn :
    Set.InjOn (fun v => t.g.molRep (t.f v)) (↑G.toMG'.int ∪ ↑G.toMG'.ext) := by
  intro v hv w hw hvw
  simp only [Set.mem_union, Finset.mem_coe] at hv hw
  have hrep : ∀ v, v ∈ G.toMG'.int ∨ v ∈ G.toMG'.ext → G.molRep v = v := by
    rintro v (hv | hv)
    · obtain ⟨a, rfl⟩ := Local_mem_int.1 hv
      exact (Local_molRep_eq_iff _ _ _).2 (G.sameMol_equivalence.symm (Local_molRep_spec G _))
    · rw [Local_mem_ext] at hv
      cases v with
      | inl a => rfl
      | inr b => simp at hv
  have := (Local_merge_sameMol h v w).1 ((Local_molRep_eq_iff _ _ _).1 hvw)
  rw [← hrep v hv, ← hrep w hw]
  exact (Local_molRep_eq_iff _ _ _).2 this

private theorem Local_merge_intEq :
    t.g.toMG'.int = G.toMG'.int.image fun v => t.g.molRep (t.f v) := by
  have hs := Local_mergeT_spec h
  obtain ⟨g, hg, hgs⟩ := hs.f_inr
  ext w
  simp only [Local_mem_int, Finset.mem_image]
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨i, rfl⟩ := hgs c
    exact ⟨G.molRep (.inr i), ⟨i, rfl⟩, by rw [Local_merge_molRep h, hg]⟩
  · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
    exact ⟨g i, by rw [Local_merge_molRep h, hg]⟩

private theorem Local_merge_extEq :
    t.g.toMG'.ext = G.toMG'.ext.image fun v => t.g.molRep (t.f v) := by
  ext w
  simp only [Graph.toMG', Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨.inl a, ⟨a, rfl⟩, by rw [Local_merge_f_inl h a]; rfl⟩
  · rintro ⟨v, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, by rw [Local_merge_f_inl h a]; rfl⟩

/-- The molecular graph of the graph of `Graph.mergeT` is carried from that of `G`, on a graph whose
blocks with two or more atoms contain an internal atom and whose solid edges have a first atom in a
block with an internal atom. -/
private theorem Local_merge_carry [NeZero k]
    (hE1 : ∀ u v : Atom k n, u ≠ v → G.SameBlock u v → ∃ b : Fin n, G.SameBlock u (.inr b)) :
    Local_Carry G.toMG' t.g.toMG' (fun v => t.g.molRep (t.f v)) := by
  set F := fun v => t.g.molRep (t.f v) with hF
  have hFρ : ∀ u, Local_rho t.g (t.f u) = F (Local_rho G u) := Local_merge_rho h
  have hpin : ∀ a, Local_Same (Local_edMap F (Local_pin G a)) (Local_pin t.g a) := by
    intro a
    by_cases hU : G.Unpinned (.inl a)
    · have hU' : t.g.Unpinned (.inl a) := by
        rw [← Local_merge_f_inl h a]
        exact (Local_merge_unpinned h _).2 hU
      have e1 : G.anchor (.inl a) = none := Local_anchor_none.2 hU.2
      have e2 : t.g.anchor (.inl a) = none := Local_anchor_none.2 hU'.2
      left
      simp [Local_pin, Local_edMap, e1, e2]
    · obtain ⟨b, hb⟩ : ∃ b, G.anchor (.inl a) = some b := by
        rcases hA : G.anchor (.inl a) with _ | b
        · exact absurd ⟨rfl, Local_anchor_none.1 hA⟩ hU
        · exact ⟨b, rfl⟩
      have hU' : ¬ t.g.Unpinned (.inl a) := by
        rw [← Local_merge_f_inl h a]
        exact fun h' => hU ((Local_merge_unpinned h _).1 h')
      obtain ⟨b', hb'⟩ : ∃ b', t.g.anchor (.inl a) = some b' := by
        rcases hA : t.g.anchor (.inl a) with _ | b'
        · exact absurd ⟨rfl, Local_anchor_none.1 hA⟩ hU'
        · exact ⟨b', rfl⟩
      right
      refine ⟨by simp [Local_pin, Local_edMap, hb, hb'], Or.inl ?_⟩
      simp only [Local_pin, Local_edMap, hb, hb', hF]
      congr 1
      · have hbb := Local_anchor_some hb
        have hbb' := Local_anchor_some hb'
        obtain ⟨c, hc⟩ := Local_merge_int h (.inr b) rfl
        have hbc : t.g.SameBlock (.inl a) (.inr c) := by
          rw [← Local_merge_f_inl h a, ← hc]
          exact (Local_merge_sameBlock h _ _).2 hbb
        rw [Local_merge_molRep h, hc]
        exact (Local_molRep_eq_iff _ _ _).2 (Or.inr ⟨rfl, rfl,
          ((hbb'.symm.trans hbc)).mono (Local_dot_le_mol _)⟩)
      · rw [Local_merge_f_inl h a]
        rfl
  have h1 := Local_carry_toRG G
  have h2 := Local_ELG_mapV (pe' := Local_pin t.g) F (G.comps.map (Local_rd G)) (Local_merge_injOn h)
    hpin (Local_rdL_vok G G.comps) (Local_pin_vok G)
  rw [← Local_merge_intEq h, ← Local_merge_extEq h, List.map_map] at h2
  have h3 := Local_ELG_filterMap' (I := t.g.toMG'.int) (X := t.g.toMG'.ext) (pe := Local_pin t.g)
    (pe' := Local_pin t.g) 0 G.comps (Local_edMap F ∘ Local_rd G)
    (Local_mergeComp (Local_mrep G) t.f) (Local_rd t.g) ?_ (fun a => Local_Same.refl _) ?_
    (Local_pin_vok t.g)
  · rw [← Local_merge_comps h] at h3
    have h4 := Local_carry_ofRG t.g
    have hc := Local_carry_trans h1 (Local_carry_trans h2 (Local_carry_trans h3 h4))
    exact hc
  · intro c hc
    refine ⟨fun hn => ?_, fun c' hc' => ?_⟩
    · obtain ⟨hk, -⟩ := Local_mergeComp_none hn
      simp [Local_edMap, Local_rd, hk]
    · rcases Local_mergeComp_some hc' with ⟨hsol, hrep, rfl⟩ | ⟨rfl, -, -⟩
      · left
        have hsb := (Local_mrep_iff G _ _).1 hrep
        have hρ : Local_rho G c.x = Local_rho G c.y := by
          by_cases hxy : c.x = c.y
          · rw [hxy]
          · exact Local_rho_block hsb (hE1 _ _ hxy hsb)
        refine ⟨by simp [Local_edMap, Local_rd, hρ], ?_⟩
        simp [Local_rd, (Local_toWeight_solid hsol).2.2.2.1]
      · right
        refine ⟨?_, Or.inl ?_⟩
        · simp only [Local_edMap, Local_rd, Function.comp_apply, Comp.map, hFρ]
          by_cases he : Local_rho G c.x = Local_rho G c.y
          · simp [he]
          · have hne : F (Local_rho G c.x) ≠ F (Local_rho G c.y) := fun h' =>
              he (Local_merge_injOn h (Or.inl (Local_rho_vtx G _) |>.elim (fun x => by
                simp only [Set.mem_union, Finset.mem_coe]; exact x) (fun x => by
                simp only [Set.mem_union, Finset.mem_coe]; exact x)) (by
                rcases Local_rho_vtx G c.y with x | x <;>
                  simp only [Set.mem_union, Finset.mem_coe] <;> simp [x]) h')
            simp [he, hne]
        · simp [Local_edMap, Local_rd, Comp.map, hFρ]
  · intro c hc
    intro hne
    exact ⟨by
      rcases Local_rho_vtx G c.x with x | x
      · exact Or.inl (by rw [Local_merge_intEq h]; exact Finset.mem_image_of_mem _ x)
      · exact Or.inr (by rw [Local_merge_extEq h]; exact Finset.mem_image_of_mem _ x), by
      rcases Local_rho_vtx G c.y with x | x
      · exact Or.inl (by rw [Local_merge_intEq h]; exact Finset.mem_image_of_mem _ x)
      · exact Or.inr (by rw [Local_merge_extEq h]; exact Finset.mem_image_of_mem _ x)⟩

private theorem Local_merge_inl_iff (u : Atom k n) (a : Fin k) : t.f u = .inl a ↔ u = .inl a := by
  constructor
  · intro hu
    cases u with
    | inl b =>
      rw [Local_merge_f_inl h b] at hu
      simp only [Sum.inl.injEq] at hu
      rw [hu]
    | inr i =>
      obtain ⟨c, hc⟩ := Local_merge_int h (.inr i) rfl
      rw [hc] at hu
      simp at hu
  · rintro rfl
    exact Local_merge_f_inl h a

private theorem Local_merge_flat_isRight (u : Atom k n) :
    (t.g.flatAtom (t.f u)).isRight = (G.flatAtom u).isRight := by
  by_cases hU : G.Unpinned u
  · rw [Local_flat_unpinned hU, Local_flat_unpinned ((Local_merge_unpinned h u).2 hU),
      Local_merge_f_int h]
  · rw [Local_flat_isRight hU, Local_flat_isRight (fun h' => hU ((Local_merge_unpinned h u).1 h'))]

private theorem Local_merge_flat_inl (u : Atom k n) (b : Fin k) :
    t.g.flatAtom (t.f u) = .inl b ↔ G.flatAtom u = .inl b := by
  by_cases hU : G.Unpinned u
  · rw [Local_flat_unpinned hU, Local_flat_unpinned ((Local_merge_unpinned h u).2 hU),
      Local_merge_inl_iff h]
  · have h1 := Local_flat_isRight hU
    have h2 := Local_flat_isRight (fun h' => hU ((Local_merge_unpinned h u).1 h'))
    constructor
    · intro he; rw [he] at h2; simp at h2
    · intro he; rw [he] at h1; simp at h1

omit h in
private theorem Local_countP_filterMap {α β : Type*} (l : List α) (ψ : α → Option β)
    (q : α → Bool) (q' : β → Bool) (hq : ∀ a ∈ l, ∀ b, ψ a = some b → q' b = true → q a = true) :
    (l.filterMap ψ).countP q' ≤ l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun a' ha' => hq a' (List.mem_cons_of_mem _ ha'))
    rcases hψ : ψ a with _ | b
    · rw [List.filterMap_cons_none hψ, List.countP_cons]
      omega
    · rw [List.filterMap_cons_some hψ, List.countP_cons, List.countP_cons]
      by_cases hb : q' b = true
      · simp [hb, hq a List.mem_cons_self b hψ hb]
        omega
      · simp [hb]
        omega


private theorem Local_merge_labAt (v : Atom k n)
    (hl : ∀ c ∈ G.comps, ∀ pq u, c.label = some (pq, u) → G.molRep u = G.molRep v) :
    ∀ c ∈ t.g.comps, ∀ pq u, c.label = some (pq, u) → t.g.molRep u = t.g.molRep (t.f v) := by
  intro c' hc' pq u' hl'
  obtain ⟨c, hc, hm⟩ := Local_merge_mem h hc'
  have hlab : c'.label = c.label.map (Prod.map id t.f) := by
    rcases Local_mergeComp_some hm with ⟨-, -, rfl⟩ | ⟨rfl, -, -⟩ <;> rfl
  rw [hlab] at hl'
  obtain ⟨⟨pq₀, u⟩, hcl, he⟩ := Option.map_eq_some_iff.1 hl'
  simp only [Prod.map, id, Prod.mk.injEq] at he
  rw [← he.2, ← Local_merge_molRep h, hl c hc pq₀ u hcl, Local_merge_molRep h]

end Spec

/-- The clauses of the graph of `Graph.mergeT` from those of `G`. -/
private theorem Local_merge_clauses {G : Graph 3 n} {t : Tracked 3 n} (h : G.mergeT = some t)
    (hC : G.ColourInvB) (hE : G.ExtClause) (hG : G.NoGhost) :
    t.g.ColourInvB ∧ t.g.ExtClause ∧ t.g.NoGhost := by
  have hs := Local_mergeT_spec h
  obtain ⟨g, hg, hgs⟩ := hs.f_inr
  have hCC := (Local_colour_iff G).1 hC
  have flatR := Local_merge_flat_isRight h
  have flatL := Local_merge_flat_inl h
  have inlI := Local_merge_inl_iff h
  have unp := Local_merge_unpinned h
  -- every component of the graph of `Graph.mergeT`
  have mem : ∀ c' ∈ t.g.comps, ∃ c ∈ G.comps, (c.kind.isSolid = true ∧
      Local_mrep G c.x = Local_mrep G c.y ∧
      c' = { (c.map t.f) with kind := c.kind.toWeight, y := t.f c.x }) ∨ c' = c.map t.f := by
    intro c' hc'
    obtain ⟨c, hc, hm⟩ := Local_merge_mem h hc'
    rcases Local_mergeComp_some hm with h1 | ⟨h1, -, -⟩
    · exact ⟨c, hc, Or.inl h1⟩
    · exact ⟨c, hc, Or.inr h1⟩
  have memk : ∀ c ∈ G.comps, c.kind.isSolid = false → c.kind ≠ .dot →
      c.map t.f ∈ t.g.comps := by
    intro c hc hs' hd
    rw [Local_merge_comps h]
    refine List.mem_filterMap.2 ⟨c, hc, ?_⟩
    unfold Local_mergeComp
    rw [if_neg (by simp [hd]), if_neg (by simp [hs'])]
  -- the charge pattern
  have hColour : t.g.ColourInvB := by
    refine (Local_colour_iff t.g).2 fun c' hc' => ?_
    obtain ⟨c, hc, ⟨hsol, -, rfl⟩ | rfl⟩ := mem c' hc'
    · obtain ⟨-, -, hr, -, -, -, -, -⟩ := Local_toWeight_solid hsol
      have hcr : c.kind.isRandom = true := (Local_solid_kinds hsol).2.2.1
      have a1 := ((hCC c hc).1 hcr).1
      have e : (t.g.flatAtom (t.f c.x)).isRight = true := by rw [flatR]; exact a1
      refine ⟨fun _ => ⟨e, ?_, ?_, ?_⟩, fun hw => ?_⟩
      · intro he; rw [he] at e; simp at e
      · intro he; rw [he] at e; simp at e
      · intro he; rw [he] at e; simp at e
      · exfalso
        have : c.kind.toWeight.isRandom = true := hr
        simp only at hw
        rw [hw] at this
        simp [Kind.isRandom] at this
    · obtain ⟨b1, b2⟩ := hCC c hc
      refine ⟨fun hr => ?_, fun hw => ?_⟩
      · obtain ⟨a1, a2, a3, a4⟩ := b1 hr
        refine ⟨?_, ?_, ?_, ?_⟩
        · change (t.g.flatAtom (t.f c.x)).isRight = true
          rw [flatR]; exact a1
        · change t.g.flatAtom (t.f c.y) ≠ _
          rw [Ne, flatL]; exact a2
        · change t.g.flatAtom (t.f c.y) = _ → _
          rw [flatL]; exact a3
        · change t.g.flatAtom (t.f c.y) = _ → _
          rw [flatL]; exact a4
      · obtain ⟨a1, a2⟩ := b2 hw
        exact ⟨by change (t.g.flatAtom (t.f c.x)).isRight = true; rw [flatR]; exact a1,
          by change (t.g.flatAtom (t.f c.y)).isRight = true; rw [flatR]; exact a2⟩
  -- no ghost edge
  have hNG : t.g.NoGhost := by
    intro c' hc'
    obtain ⟨c, hc, ⟨hsol, -, rfl⟩ | rfl⟩ := mem c' hc'
    · exact (Local_toWeight_solid hsol).2.2.2.2.2.1
    · exact hG c hc
  -- the clause on the external atoms
  obtain ⟨E1, E2, E3, E4, E5⟩ := hE
  have diffm : ∀ c' ∈ t.g.comps, c'.kind.isDiffusive = true → ∃ c ∈ G.comps, c' = c.map t.f := by
    intro c' hc' hd
    obtain ⟨c, hc, ⟨hsol, -, rfl⟩ | rfl⟩ := mem c' hc'
    · exact absurd hd (by rw [(Local_toWeight_solid hsol).2.2.2.2.2.2.1]; simp)
    · exact ⟨c, hc, rfl⟩
  have hns : ∀ κ : Kind, κ.isDiffusive = true → κ.isSolid = false ∧ κ ≠ .dot := by
    intro κ h
    cases κ <;> simp [Kind.isDiffusive, Kind.isSolid] at h ⊢
  have hdp : ∀ a : Fin 3, G.HasDiffToPinned (.inl a) → t.g.HasDiffToPinned (.inl a) := by
    rintro a ⟨c, hc, hd, hor⟩
    refine ⟨c.map t.f, memk c hc (hns _ hd).1 (hns _ hd).2, hd, ?_⟩
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by simp [Comp.map, h1, Local_merge_f_inl h], by
        change ¬ t.g.Unpinned (t.f c.y); rw [unp]; exact h2⟩
    · exact Or.inr ⟨by simp [Comp.map, h1, Local_merge_f_inl h], by
        change ¬ t.g.Unpinned (t.f c.x); rw [unp]; exact h2⟩
  have hdt : ∀ a : Fin 3, G.DiffToPinned (.inl a) → t.g.DiffToPinned (.inl a) := by
    intro a hdt c' hc' hd
    obtain ⟨c, hc, rfl⟩ := diffm c' hc' hd
    obtain ⟨h1, h2⟩ := hdt c hc hd
    refine ⟨fun hx => ?_, fun hy => ?_⟩
    · change ¬ t.g.Unpinned (t.f c.y)
      rw [unp]
      exact h1 ((inlI c.x a).1 hx)
    · change ¬ t.g.Unpinned (t.f c.x)
      rw [unp]
      exact h2 ((inlI c.y a).1 hy)
  have deg_le : ∀ a : Fin 3, t.g.nonDotDeg (.inl a) ≤ G.nonDotDeg (.inl a) := by
    intro a
    unfold Graph.nonDotDeg
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter, Local_merge_comps h]
    refine Local_countP_filterMap _ _ _ _ fun c hc c' hm hq => ?_
    simp only [decide_eq_true_eq] at hq ⊢
    rcases Local_mergeComp_some hm with ⟨hsol, -, rfl⟩ | ⟨rfl, -, -⟩
    · obtain ⟨hdot, -, -, -, hxd, -⟩ := Local_toWeight_solid hsol
      have hk : c.kind ≠ .dot ∧ c.kind ≠ .xdot :=
        ⟨(Local_solid_kinds hsol).1, (Local_solid_kinds hsol).2.1⟩
      refine ⟨?_, hk⟩
      simp only at hq
      rcases hq.1 with h' | h' <;> exact Or.inl ((inlI c.x a).1 h')
    · simp only [Comp.map] at hq
      refine ⟨?_, hq.2⟩
      rcases hq.1 with h' | h'
      · exact Or.inl ((inlI c.x a).1 h')
      · exact Or.inr ((inlI c.y a).1 h')
  have unpE : ∀ a : Fin 3, t.g.Unpinned (.inl a) ↔ G.Unpinned (.inl a) := fun a => by
    rw [← Local_merge_f_inl h a]
    exact unp _
  have hExt : t.g.ExtClause := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro u' v' hne hb
      obtain ⟨u, rfl⟩ := hs.f_surj u'
      obtain ⟨v, rfl⟩ := hs.f_surj v'
      have huv : u ≠ v := fun e => hne (by rw [e])
      obtain ⟨b, hb'⟩ := E1 u v huv ((Local_merge_sameBlock h u v).1 hb)
      exact ⟨g b, by rw [← hg]; exact (Local_merge_sameBlock h u (.inr b)).2 hb'⟩
    · intro c' hc' hk
      obtain ⟨c, hc, ⟨hsol, -, rfl⟩ | rfl⟩ := mem c' hc'
      · exact absurd hk (Local_toWeight_solid hsol).2.2.2.2.1
      · rintro ⟨h1, h2⟩
        exact E2 c hc hk ⟨(unp c.x).1 h1, (unp c.y).1 h2⟩
    · intro hU
      obtain ⟨a1, a2⟩ := E3 ((unpE 0).1 hU)
      exact ⟨hdp 0 a1, hdt 0 a2⟩
    · intro hU
      obtain ⟨a1, a2⟩ := E4 ((unpE 2).1 hU)
      refine ⟨fun c' hc' hd => ?_, le_trans (deg_le 2) a2⟩
      obtain ⟨c, hc, rfl⟩ := diffm c' hc' hd
      obtain ⟨b1, b2⟩ := a1 c hc hd
      exact ⟨fun h' => b1 ((inlI _ _).1 h'), fun h' => b2 ((inlI _ _).1 h')⟩
    · intro hU
      have hU' := (unpE 1).1 hU
      obtain ⟨a1, a2, a3⟩ := E5 hU'
      refine ⟨?_, hdt 1 a2, le_trans (deg_le 1) a3⟩
      rcases a1 with ⟨c, hc, hk, hor⟩ | h'
      · left
        have hcr : c.kind.isRandom = true := by rw [hk]; rfl
        have hcx : (G.flatAtom c.x).isRight = true := ((hCC c hc).1 hcr).1
        have hx1 : c.x ≠ .inl 1 := by
          intro hx
          rw [hx, Local_flat_unpinned hU'] at hcx
          simp at hcx
        have hy1 : c.y = .inl 1 := hor.resolve_left hx1
        have hrep : Local_mrep G c.x ≠ Local_mrep G c.y := by
          intro he
          have hsb := (Local_mrep_iff G _ _).1 he
          rw [hy1] at hsb
          obtain ⟨b, hb⟩ : ∃ b, G.flatAtom c.x = .inr b := by
            rcases hf : G.flatAtom c.x with a | b
            · rw [hf] at hcx; simp at hcx
            · exact ⟨b, rfl⟩
          have hfb : G.SameBlock c.x (.inr b) := hb ▸ Local_flat_block G c.x
          exact hU'.2 b (hsb.symm.trans hfb)
        have hm : Local_mergeComp (Local_mrep G) t.f c = some (c.map t.f) := by
          unfold Local_mergeComp
          rw [if_neg (by simp [hk]), if_neg (by simp [hrep])]
        refine ⟨c.map t.f, ?_, hk, Or.inr ?_⟩
        · rw [Local_merge_comps h]
          exact List.mem_filterMap.2 ⟨c, hc, hm⟩
        · simp [Comp.map, hy1, Local_merge_f_inl h]
      · exact Or.inr (hdp 1 h')
  exact ⟨hColour, hExt, hNG⟩

end MergeRead

/-! ## One added dotted edge -/

section AddDot

variable {k n : ℕ}

/-- The graph `Γ` with the dotted edge `p = q` added. -/
private def Local_addG (Γ : Graph k n) (p q : Atom k n) : Graph k n :=
  ⟨Γ.comps ++ [mkC .dot p q], Γ.coeff⟩

private theorem Local_fromRel_add (P : Comp (Atom k n) → Prop) (l : List (Comp (Atom k n)))
    (d : Comp (Atom k n)) (hd : P d) (u v : Atom k n) :
    (SimpleGraph.fromRel fun u v => ∃ c ∈ l ++ [d], P c ∧ c.x = u ∧ c.y = v).Adj u v ↔
      (SimpleGraph.fromRel fun u v => ∃ c ∈ l, P c ∧ c.x = u ∧ c.y = v).Adj u v ∨
        (u ≠ v ∧ (u = d.x ∧ v = d.y ∨ u = d.y ∧ v = d.x)) := by
  simp only [SimpleGraph.fromRel_adj, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hne, ⟨c, hc | rfl, hk, rfl, rfl⟩ | ⟨c, hc | rfl, hk, rfl, rfl⟩⟩
    · exact Or.inl ⟨hne, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩
    · exact Or.inr ⟨hne, Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨hne, Or.inr ⟨c, hc, hk, rfl, rfl⟩⟩
    · exact Or.inr ⟨hne, Or.inr ⟨rfl, rfl⟩⟩
  · rintro (⟨hne, ⟨c, hc, hk, rfl, rfl⟩ | ⟨c, hc, hk, rfl, rfl⟩⟩ | ⟨hne, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · exact ⟨hne, Or.inl ⟨c, Or.inl hc, hk, rfl, rfl⟩⟩
    · exact ⟨hne, Or.inr ⟨c, Or.inl hc, hk, rfl, rfl⟩⟩
    · exact ⟨hne, Or.inl ⟨d, Or.inr rfl, hd, rfl, rfl⟩⟩
    · exact ⟨hne, Or.inr ⟨d, Or.inr rfl, hd, rfl, rfl⟩⟩

private theorem Local_reach_add {V : Type} {G G' : SimpleGraph V} (p q : V) (hle : G ≤ G')
    (hpq : G'.Reachable p q)
    (hadj : ∀ u v, G'.Adj u v → G.Adj u v ∨ (u = p ∧ v = q ∨ u = q ∧ v = p))
    (u v : V) :
    G'.Reachable u v ↔ G.Reachable u v ∨ (G.Reachable u p ∧ G.Reachable q v) ∨
      (G.Reachable u q ∧ G.Reachable p v) := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact Or.inl (SimpleGraph.Reachable.refl _)
    | @cons a b c h w ih =>
      rcases hadj _ _ h with h' | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases ih with h3 | ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inl (h'.reachable.trans h3)
        · exact Or.inr (Or.inl ⟨h'.reachable.trans h3, h4⟩)
        · exact Or.inr (Or.inr ⟨h'.reachable.trans h3, h4⟩)
      · subst h1 h2
        rcases ih with h3 | ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h3⟩)
        · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h4⟩)
        · exact Or.inl h4
      · subst h1 h2
        rcases ih with h3 | ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, h3⟩)
        · exact Or.inl h4
        · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, h4⟩)
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact SimpleGraph.Reachable.mono hle h
    · exact (SimpleGraph.Reachable.mono hle h1).trans
        (hpq.trans (SimpleGraph.Reachable.mono hle h2))
    · exact (SimpleGraph.Reachable.mono hle h1).trans
        (hpq.symm.trans (SimpleGraph.Reachable.mono hle h2))

private theorem Local_add_sameBlock (Γ : Graph k n) (p q u v : Atom k n) :
    (Local_addG Γ p q).SameBlock u v ↔ Γ.SameBlock u v ∨ (Γ.SameBlock u p ∧ Γ.SameBlock q v) ∨
      (Γ.SameBlock u q ∧ Γ.SameBlock p v) := by
  have hadj := Local_fromRel_add (fun c => c.kind = .dot) Γ.comps (mkC .dot p q) rfl
  refine Local_reach_add (G := Γ.dotGraph) (G' := (Local_addG Γ p q).dotGraph) p q ?_ ?_ ?_ u v
  · intro a b h
    exact (hadj a b).2 (Or.inl h)
  · by_cases hpq : p = q
    · subst hpq
      exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable ((hadj p q).2 (Or.inr ⟨hpq, Or.inl ⟨rfl, rfl⟩⟩))
  · intro a b h
    rcases (hadj a b).1 h with h | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h

private theorem Local_add_molReach (Γ : Graph k n) (p q u v : Atom k n) :
    (Local_addG Γ p q).molGraph.Reachable u v ↔ Γ.molGraph.Reachable u v ∨
      (Γ.molGraph.Reachable u p ∧ Γ.molGraph.Reachable q v) ∨
      (Γ.molGraph.Reachable u q ∧ Γ.molGraph.Reachable p v) := by
  have hadj := Local_fromRel_add (fun c => c.kind.joinsMol = true) Γ.comps (mkC .dot p q) rfl
  refine Local_reach_add (G := Γ.molGraph) (G' := (Local_addG Γ p q).molGraph) p q ?_ ?_ ?_ u v
  · intro a b h
    exact (hadj a b).2 (Or.inl h)
  · by_cases hpq : p = q
    · subst hpq
      exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable ((hadj p q).2 (Or.inr ⟨hpq, Or.inl ⟨rfl, rfl⟩⟩))
  · intro a b h
    rcases (hadj a b).1 h with h | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h

variable {Γ : Graph k n} {p q : Atom k n}

private theorem Local_add_sameBlock_mono {u v : Atom k n} (h : Γ.SameBlock u v) :
    (Local_addG Γ p q).SameBlock u v :=
  (Local_add_sameBlock Γ p q u v).2 (Or.inl h)

private theorem Local_add_sameMol_mono {u v : Atom k n} (h : Γ.SameMol u v) :
    (Local_addG Γ p q).SameMol u v := by
  rcases h with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, (Local_add_molReach Γ p q u v).2 (Or.inl h3)⟩

private theorem Local_add_sameBlock_pq : (Local_addG Γ p q).SameBlock p q :=
  (Local_add_sameBlock Γ p q p q).2
    (Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, SimpleGraph.Reachable.refl _⟩))

private theorem Local_add_molRep_molRep (v : Atom k n) :
    (Local_addG Γ p q).molRep (Γ.molRep v) = (Local_addG Γ p q).molRep v :=
  (Local_molRep_eq_iff _ _ _).2
    (Local_add_sameMol_mono (Γ.sameMol_equivalence.symm (Local_molRep_spec Γ v)))

private theorem Local_add_unpinned_of {u : Atom k n} (h : (Local_addG Γ p q).Unpinned u) :
    Γ.Unpinned u :=
  ⟨h.1, fun b hb => h.2 b (Local_add_sameBlock_mono hb)⟩

private theorem Local_add_unpinned {u : Atom k n} {b₀ : Fin n} (hp : Γ.SameBlock p (.inr b₀))
    (h : Γ.Unpinned u) (hq : ¬ Γ.SameBlock u q) : (Local_addG Γ p q).Unpinned u := by
  refine ⟨h.1, fun b hb => ?_⟩
  rcases (Local_add_sameBlock Γ p q _ _).1 hb with h1 | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h.2 b h1
  · exact h.2 b₀ (h1.trans hp)
  · exact hq h1

/-- Away from an unpinned atom in the block of `q`, the reading after the dotted edge is added is
the molecule of the reading before. -/
private theorem Local_add_rho {u : Atom k n} {b₀ : Fin n} (hp : Γ.SameBlock p (.inr b₀))
    (hu : ¬ (Γ.Unpinned u ∧ Γ.SameBlock u q)) :
    Local_rho (Local_addG Γ p q) u = (Local_addG Γ p q).molRep (Local_rho Γ u) := by
  unfold Local_rho
  rw [Local_add_molRep_molRep]
  by_cases h : Γ.Unpinned u
  · have hq : ¬ Γ.SameBlock u q := fun h' => hu ⟨h, h'⟩
    rw [Local_flat_unpinned (Local_add_unpinned hp h hq), Local_flat_unpinned h]
  · have hr := Local_flat_isRight h
    obtain ⟨c, hc⟩ : ∃ c, Γ.flatAtom u = .inr c := by
      cases hf : Γ.flatAtom u with
      | inl a => rw [hf] at hr; simp at hr
      | inr c => exact ⟨c, rfl⟩
    have hb : Γ.SameBlock u (.inr c) := hc ▸ Local_flat_block Γ u
    rw [hc]
    exact Local_molRep_flat (Local_add_sameBlock_mono hb)

/-- The atom `q` is read at the molecule of `p` after the dotted edge is added. -/
private theorem Local_add_rho_q {b₀ : Fin n} (hp : Γ.SameBlock p (.inr b₀)) :
    Local_rho (Local_addG Γ p q) q = (Local_addG Γ p q).molRep (.inr b₀) :=
  Local_molRep_flat (Local_add_sameBlock_pq.symm.trans (Local_add_sameBlock_mono hp))

end AddDot

/-- Two entries of a list at increasing positions form a sublist. -/
private theorem Local_sub2 {α : Type*} :
    ∀ (l : List α) (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i < j →
      [l[i], l[j]].Sublist l
  | [], _, _, hi, _, _ => absurd hi (by simp)
  | a :: l, 0, j + 1, _, hj, _ =>
    List.Sublist.cons₂ a (List.singleton_sublist.2 (List.getElem_mem _))
  | a :: l, i + 1, j + 1, hi, hj, hij =>
    List.Sublist.cons a (Local_sub2 l i j (by simpa using hi) (by simpa using hj) (by omega))
  | _ :: _, _, 0, _, _, hij => absurd hij (by omega)

/-- Two distinct positions whose entries satisfy `p`: the count is at least two. -/
private theorem Local_two_le_countP {α : Type*} (l : List α) (p : α → Bool) (i j : Fin l.length)
    (hij : i ≠ j) (hi : p l[i] = true) (hj : p l[j] = true) : 2 ≤ l.countP p := by
  have hi' : p l[(i : ℕ)] = true := hi
  have hj' : p l[(j : ℕ)] = true := hj
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · have := (Local_sub2 l i j i.2 j.2 h).countP_le (p := p)
    simp only [List.countP_cons, List.countP_nil, hi', hj', if_true] at this
    omega
  · have := (Local_sub2 l j i j.2 i.2 h).countP_le (p := p)
    simp only [List.countP_cons, List.countP_nil, hi', hj', if_true] at this
    omega

section AddPull

variable {n : ℕ}

/-- The pin edge of an external atom (an arbitrary edge at an internal atom). -/
private def Local_pinT {m : ℕ} (q : Atom 3 n) : Fin m ⊕ Fin 3 :=
  match q with
  | .inl aq => .inr aq
  | .inr _ => .inr 0

private theorem Local_pinClass_ne {a : Fin 3} (h : a ≠ 2) : pinClass a ≠ .minus := by
  unfold pinClass
  split_ifs with h1 h2
  · simp
  · exact absurd (Fin.ext h2) h
  · simp

/-- A red solid edge at an unpinned external atom ends at `⊖`. -/
private theorem Local_red_at {Γ : Graph 3 n} (hC : Γ.ColourInvB) {c : Comp (Atom 3 n)}
    (hc : c ∈ Γ.comps) (hk : c.kind = .G .minus) {u : Atom 3 n} (hU : Γ.Unpinned u)
    (hq : c.x = u ∨ c.y = u) : u = .inl 2 ∧ c.y = u := by
  obtain ⟨aq, hqa⟩ : ∃ aq, u = .inl aq := by
    have := hU.1
    rcases hq : u with a | b
    · exact ⟨a, rfl⟩
    · rw [hq] at this; simp at this
  have hr' : c.kind.isRandom = true := by rw [hk]; rfl
  obtain ⟨a1, a2, a3, -⟩ := ((Local_colour_iff Γ).1 hC c hc).1 hr'
  have hfl := Local_flat_unpinned hU
  have hx : c.x ≠ u := by
    intro hx
    rw [hx, hfl, hqa] at a1
    simp at a1
  have hy : c.y = u := hq.resolve_left hx
  refine ⟨?_, hy⟩
  rw [hy, hfl, hqa] at a2 a3
  have h0 : aq ≠ 0 := fun h => a2 (by rw [h])
  have h1 : aq ≠ 1 := fun h => by have := a3 (by rw [h]); rw [hk] at this; simp at this
  have : aq = 2 := by omega
  rw [hqa, this]

set_option maxHeartbeats 1000000 in
/-- [II, Lemma 5.10] for one added dotted edge, the isolated subsets: every proper isolated subset
after a dotted edge `p = q` is added at an atom `p` of a block with an internal atom, on a graph
with the charge pattern of the block normal form, the clause on the external atoms and no ghost
edge, is read back as a proper isolated subset before, and is weakly isolated when it is. -/
private theorem Local_add_pull {Γ : Graph 3 n} {p q : Atom 3 n} {b₀ : Fin n}
    (hp : Γ.SameBlock p (.inr b₀)) (hC : Γ.ColourInvB) (hE : Γ.ExtClause) (hG : Γ.NoGhost)
    (hs : spdPM' Γ) (hs' : spdPM' (Local_addG Γ p q)) :
    Local_Pull Γ.toMG' (Local_addG Γ p q).toMG' (Local_addG Γ p q).molRep := by
  set Γ' := Local_addG Γ p q with hΓ'
  set φ := Γ'.molRep with hφ
  have hCC := (Local_colour_iff Γ).1 hC
  have hlen : Γ'.comps.length = Γ.comps.length + 1 := by simp [hΓ', Local_addG]
  let ι : Fin Γ.comps.length → Fin Γ'.comps.length := fun i => ⟨i, by omega⟩
  have hget : ∀ i : Fin Γ.comps.length, Γ'.comps[ι i] = Γ.comps[i] := by
    intro i
    simp [ι, hΓ', Local_addG, List.getElem_append_left]
  have hnew : ∀ u, Γ.Unpinned u → Γ.SameBlock u q → u = q := by
    intro u hu hq
    by_contra hne
    obtain ⟨b, hb⟩ := hE.1 u q hne hq
    exact hu.2 b hb
  set B := Γ'.molRep (.inr b₀) with hB
  have hρq : Local_rho Γ' q = B := Local_add_rho_q hp
  have hρ : ∀ u, ¬ (u = q ∧ Γ.Unpinned q) → Local_rho Γ' u = φ (Local_rho Γ u) := by
    intro u hu
    refine Local_add_rho hp fun ⟨h1, h2⟩ => hu ⟨hnew u h1 h2, ?_⟩
    rw [← hnew u h1 h2]
    exact h1
  have hdisj := Graph.toMG'_disjoint Γ'
  have hdc' : Γ'.toMG'.DC := hs'.1
  -- vertices
  have hφint : ∀ v ∈ Γ.toMG'.int, φ v ∈ Γ'.toMG'.int := by
    intro v hv
    obtain ⟨a, rfl⟩ := Local_mem_int.1 hv
    rw [hφ, Local_add_molRep_molRep]
    exact Local_mem_int.2 ⟨a, rfl⟩
  have hφext : ∀ v ∈ Γ.toMG'.ext, φ v = v := by
    intro v hv
    rw [Local_mem_ext] at hv
    cases v with
    | inl a => rfl
    | inr b => simp at hv
  refine Local_pull_of φ hφint (fun w hw => ?_) hs.1 fun P' hP'' => ?_
  · obtain ⟨a, rfl⟩ := Local_mem_int.1 hw
    exact ⟨Γ.molRep (.inr a), Local_mem_int.2 ⟨a, rfl⟩, by rw [hφ, Local_add_molRep_molRep]⟩
  obtain ⟨hiso, hlt⟩ := hP''
  have hP' : P' ⊆ Γ'.toMG'.int := hiso.1
  set P := Γ.toMG'.int.filter fun v => φ v ∈ P' with hP
  -- a vertex of `Γ` lies in `P` exactly when its image lies in `P'`
  have hmemP : ∀ v, Γ.toMG'.IsVtx v → (v ∈ P ↔ φ v ∈ P') := by
    rintro v (hv | hv)
    · simp [hP, hv]
    · rw [hφext v hv]
      have h1 : v ∉ P := fun h =>
        Finset.disjoint_left.1 (Graph.toMG'_disjoint Γ) (Finset.filter_subset _ _ h) hv
      have hv' : v ∈ Γ'.toMG'.ext := by rw [Local_mem_ext] at hv ⊢; exact hv
      have h2 : v ∉ P' := fun h => Finset.disjoint_left.1 hdisj (hP' h) hv'
      exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  have hvtx' : ∀ v, Γ.toMG'.IsVtx v → Γ'.toMG'.IsVtx (φ v) := by
    rintro v (hv | hv)
    · exact Or.inl (hφint v hv)
    · rw [hφext v hv]
      exact Or.inr (by rw [Local_mem_ext]; rw [Local_mem_ext] at hv; exact hv)
  -- the reading of the pin edge of `q` once `q` is identified with `p`
  have hpinq : ∀ a, q = .inl a → Γ'.toMG'.cls (.inr a) = some (pinClass a) ∧
      Γ'.toMG'.ends (.inr a) = (B, q) := by
    intro a ha
    have hsb : Γ'.SameBlock (.inl a) (.inr b₀) := by
      rw [← ha]
      exact Local_add_sameBlock_pq.symm.trans (Local_add_sameBlock_mono hp)
    obtain ⟨hc1, he1⟩ := Local_toMG'_pin Γ' a
    rcases hA : Γ'.anchor (.inl a) with _ | b
    · exact absurd hsb (Local_anchor_none.1 hA b₀)
    · have hb := Local_anchor_some hA
      refine ⟨by rw [hc1]; simp [Local_pin, hA], ?_⟩
      have e2 : (Local_pin Γ' a).2 = (Γ'.molRep (.inr b), .inl a) := by simp [Local_pin, hA]
      rw [he1, e2, ha]
      have e3 : Γ'.molRep (.inr b) = B := (Local_molRep_eq_iff _ _ _).2 (Or.inr ⟨rfl, rfl,
        (hb.symm.trans hsb).mono (Local_dot_le_mol _)⟩)
      rw [e3]
  -- a non-red present edge of `Γ'` at the vertex `B ∈ P'` to the external `q`: not isolated
  have hnotB : ∀ a, q = .inl a → Γ.Unpinned q → pinClass a ≠ .minus → B ∉ P' := by
    intro a ha hU hpc hBP
    obtain ⟨hc1, he1⟩ := hpinq a ha
    have hnt : ¬ Γ'.toMG'.int ⊆ P' := fun h => (ne_of_ssubset hlt) (hP'.antisymm h)
    refine Local_not_iso_ext hdc' hP' ⟨B, hBP⟩ hnt (e := .inr a) (by rw [hc1]; simp)
      (by rw [hc1]; simpa using hpc) (by rw [he1]; exact hBP)
      (by rw [he1]; exact Or.inr (by rw [Local_mem_ext, ha]; rfl)) (by
        rw [he1]
        intro h
        exact Finset.disjoint_left.1 hdisj h (by rw [Local_mem_ext, ha]; rfl)) hiso
  -- the edges of the components
  have hcomp : ∀ i : Fin Γ.comps.length, Γ.toMG'.cls (.inl i) = (Local_rd Γ Γ.comps[i]).1 ∧
      (Γ.toMG'.cls (.inl i) ≠ none → Γ.toMG'.ends (.inl i) = (Local_rd Γ Γ.comps[i]).2) :=
    Local_toMG'_cls Γ
  have hcomp' : ∀ i : Fin Γ.comps.length,
      Γ'.toMG'.cls (.inl (ι i)) = (Local_rd Γ' Γ.comps[i]).1 ∧
      (Γ'.toMG'.cls (.inl (ι i)) ≠ none →
        Γ'.toMG'.ends (.inl (ι i)) = (Local_rd Γ' Γ.comps[i]).2) := by
    intro i
    rw [← hget i]
    exact Local_toMG'_cls Γ' (ι i)
  -- the reading of an unpinned external atom is the atom
  have hρU : ∀ u, Γ.Unpinned u → Local_rho Γ u = u := by
    intro u hu
    unfold Local_rho
    rw [Local_flat_unpinned hu]
    cases u with
    | inl a => rfl
    | inr b => simp [Graph.Unpinned] at hu
  have hUP : ∀ u, Γ.Unpinned u → u ∉ P := by
    intro u hu h
    have h1 := Finset.filter_subset _ _ h
    have h2 : u ∈ Γ.toMG'.ext := by
      rw [Local_mem_ext]
      exact hu.1
    exact Finset.disjoint_left.1 (Graph.toMG'_disjoint Γ) h1 h2
  -- the pins of `Γ`
  have hpin' : ∀ a, Γ.toMG'.cls (.inr a) ≠ none → Γ'.toMG'.cls (.inr a) = Γ.toMG'.cls (.inr a) ∧
      Γ'.toMG'.ends (.inr a) = (φ (Γ.toMG'.ends (.inr a)).1, φ (Γ.toMG'.ends (.inr a)).2) := by
    intro a ha
    obtain ⟨c1, e1⟩ := Local_toMG'_pin Γ a
    obtain ⟨c1', e1'⟩ := Local_toMG'_pin Γ' a
    rcases hA : Γ.anchor (.inl a) with _ | b
    · exfalso; apply ha; rw [c1]; simp [Local_pin, hA]
    · have hb := Local_anchor_some hA
      have hb' : Γ'.SameBlock (.inl a) (.inr b) := Local_add_sameBlock_mono hb
      rcases hA' : Γ'.anchor (.inl a) with _ | b'
      · exact absurd hb' (Local_anchor_none.1 hA' b)
      · have hbb' := Local_anchor_some hA'
        refine ⟨by rw [c1, c1']; simp [Local_pin, hA, hA'], ?_⟩
        rw [e1, e1']
        simp only [Local_pin, hA, hA']
        refine Prod.ext ?_ rfl
        rw [hφ, Local_add_molRep_molRep]
        exact (Local_molRep_eq_iff _ _ _).2 (Or.inr ⟨rfl, rfl,
          (hbb'.symm.trans hb').mono (Local_dot_le_mol _)⟩)
  -- the image of a cut of `P` with ends read in the same way
  have hcutφ : ∀ a b : Atom 3 n, Γ.toMG'.IsVtx a → Γ.toMG'.IsVtx b →
      ((a ∈ P ∧ b ∉ P) ∨ (a ∉ P ∧ b ∈ P)) → ((φ a ∈ P' ∧ φ b ∉ P') ∨ (φ a ∉ P' ∧ φ b ∈ P')) := by
    intro a b ha hb h
    rw [← hmemP a ha, ← hmemP b hb]
    exact h
  -- an edge `.inl i` present in `Γ` with no end at a newly identified `q`
  have hkeep : ∀ i : Fin Γ.comps.length, Γ.toMG'.cls (.inl i) ≠ none →
      Γ.toMG'.Cut P (.inl i) → ¬ (Γ.Unpinned q ∧ (Γ.comps[i].x = q ∨ Γ.comps[i].y = q)) →
      Γ'.toMG'.cls (.inl (ι i)) = Γ.toMG'.cls (.inl i) ∧ Γ'.toMG'.IsVtx (Γ'.toMG'.ends (.inl (ι i))).1 ∧
        Γ'.toMG'.IsVtx (Γ'.toMG'.ends (.inl (ι i))).2 ∧ Γ'.toMG'.Cut P' (.inl (ι i)) := by
    intro i hc hcut hni
    have h1 : Local_rho Γ' Γ.comps[i].x = φ (Local_rho Γ Γ.comps[i].x) :=
      hρ _ fun ⟨h1, h2⟩ => hni ⟨h2, Or.inl h1⟩
    have h2 : Local_rho Γ' Γ.comps[i].y = φ (Local_rho Γ Γ.comps[i].y) :=
      hρ _ fun ⟨h1, h2⟩ => hni ⟨h2, Or.inr h1⟩
    unfold MGraph.Cut at hcut
    rw [(hcomp i).2 hc] at hcut
    have hcut' := hcutφ _ _ (Local_rho_vtx Γ _) (Local_rho_vtx Γ _) hcut
    have hne : φ (Local_rho Γ Γ.comps[i].x) ≠ φ (Local_rho Γ Γ.comps[i].y) := by
      intro h
      rw [h] at hcut'
      rcases hcut' with ⟨a, b⟩ | ⟨a, b⟩ <;> contradiction
    have hne0 : Local_rho Γ Γ.comps[i].x ≠ Local_rho Γ Γ.comps[i].y := fun h => hne (by rw [h])
    have hc' : Γ'.toMG'.cls (.inl (ι i)) = Γ.toMG'.cls (.inl i) := by
      rw [(hcomp' i).1, (hcomp i).1]
      show (if Γ.comps[i].kind = .dot ∨ Local_rho Γ' Γ.comps[i].x = Local_rho Γ' Γ.comps[i].y
        then none else _) = (if Γ.comps[i].kind = .dot ∨ Local_rho Γ Γ.comps[i].x =
          Local_rho Γ Γ.comps[i].y then none else _)
      rw [h1, h2]
      simp only [hne, hne0, or_false]
    have hc'' : Γ'.toMG'.cls (.inl (ι i)) ≠ none := by rw [hc']; exact hc
    have hen : Γ'.toMG'.ends (.inl (ι i)) =
        (φ (Local_rho Γ Γ.comps[i].x), φ (Local_rho Γ Γ.comps[i].y)) := by
      rw [(hcomp' i).2 hc'']
      show (Local_rho Γ' Γ.comps[i].x, Local_rho Γ' Γ.comps[i].y) = _
      rw [h1, h2]
    refine ⟨hc', ?_, ?_, ?_⟩
    · rw [hen]; exact hvtx' _ (Local_rho_vtx Γ _)
    · rw [hen]; exact hvtx' _ (Local_rho_vtx Γ _)
    · unfold MGraph.Cut
      rw [hen]
      exact hcut'
  -- an edge `.inl i` present in `Γ` with an end at a newly identified `q`: the other end
  have hatq : ∀ i : Fin Γ.comps.length, Γ.Unpinned q → (Γ.comps[i].x = q ∨ Γ.comps[i].y = q) →
      Γ.toMG'.cls (.inl i) ≠ none → Γ.toMG'.Cut P (.inl i) →
      ∃ w, w ≠ q ∧ ((Γ.comps[i].x = q ∧ Γ.comps[i].y = w) ∨ (Γ.comps[i].x = w ∧
        Γ.comps[i].y = q)) ∧ Local_rho Γ w ∈ P := by
    intro i hU hq hc hcut
    unfold MGraph.Cut at hcut
    rw [(hcomp i).2 hc] at hcut
    simp only [Local_rd] at hcut
    rcases hq with hx | hy
    · refine ⟨Γ.comps[i].y, fun hy => ?_, Or.inl ⟨hx, rfl⟩, ?_⟩
      · rw [hx, hy] at hcut
        rcases hcut with ⟨a, b⟩ | ⟨a, b⟩ <;> contradiction
      · rw [hx, hρU q hU] at hcut
        rcases hcut with ⟨a, b⟩ | ⟨a, b⟩
        · exact absurd a (hUP q hU)
        · exact b
    · refine ⟨Γ.comps[i].x, fun hx => ?_, Or.inr ⟨rfl, hy⟩, ?_⟩
      · rw [hx, hy] at hcut
        rcases hcut with ⟨a, b⟩ | ⟨a, b⟩ <;> contradiction
      · rw [hy, hρU q hU] at hcut
        rcases hcut with ⟨a, b⟩ | ⟨a, b⟩
        · exact a
        · exact absurd b (hUP q hU)
  -- a present edge at the unpinned `⊖` is a red solid edge ending at `⊖`
  have hminus : Γ.Unpinned (.inl 2) → ∀ i : Fin Γ.comps.length,
      (Γ.comps[i].x = .inl 2 ∨ Γ.comps[i].y = .inl 2) → (Local_rd Γ Γ.comps[i]).1 ≠ none →
      Γ.comps[i].kind = .G .minus ∧ Γ.comps[i].y = .inl 2 := by
    intro hU i hq hc
    have hmem : Γ.comps[i] ∈ Γ.comps := List.getElem_mem _
    obtain ⟨b1, -⟩ := hCC _ hmem
    have hmc : Γ.comps[i].kind.mclass ≠ none := by
      intro h
      apply hc
      show (if _ then none else Γ.comps[i].kind.mclass) = none
      rw [h]
      split_ifs <;> rfl
    have hfl := Local_flat_unpinned hU
    cases hk : Γ.comps[i].kind with
    | G ch =>
      have hr : Γ.comps[i].kind.isRandom = true := by rw [hk]; rfl
      obtain ⟨a1, -, a3, a4⟩ := b1 hr
      rcases hq with hx | hy
      · rw [hx, hfl] at a1; simp at a1
      · have := a4 (by rw [hy, hfl])
        rw [hk] at this
        exact ⟨this, hy⟩
    | ghost => exact absurd hk (hG _ hmem)
    | theta o =>
      have := (hE.2.2.2.1 hU).1 _ hmem (by rw [hk]; rfl)
      rcases hq with h | h
      · exact absurd h this.1
      · exact absurd h this.2
    | thetaErr a b =>
      have := (hE.2.2.2.1 hU).1 _ hmem (by rw [hk]; rfl)
      rcases hq with h | h
      · exact absurd h this.1
      · exact absurd h this.2
    | aux j r b =>
      cases b with
      | false => exact absurd (by rw [hk]; rfl) hmc
      | true =>
        have := (hE.2.2.2.1 hU).1 _ hmem (by rw [hk]; rfl)
        rcases hq with h | h
        · exact absurd h this.1
        · exact absurd h this.2
    | dot =>
      exfalso
      apply hc
      show (if Γ.comps[i].kind = .dot ∨ _ then none else _) = none
      rw [if_pos (Or.inl hk)]
    | _ => exact absurd (by rw [hk]; rfl) hmc
  -- the class of a present edge `.inl i` is the class of its kind
  have hclsK : ∀ i : Fin Γ.comps.length, Γ.toMG'.cls (.inl i) ≠ none →
      Γ.toMG'.cls (.inl i) = Γ.comps[i].kind.mclass := by
    intro i hc
    rw [(hcomp i).1] at hc ⊢
    show (if _ then none else Γ.comps[i].kind.mclass) = _
    rw [if_neg]
    intro h
    apply hc
    show (if _ then none else Γ.comps[i].kind.mclass) = none
    rw [if_pos h]
  -- a red edge at a newly identified `q`: `q` is `⊖`, the second atom
  have hqL : Γ.Unpinned q → ∃ aq, q = .inl aq := fun hU => by
    have := hU.1
    rcases hq : q with a | b
    · exact ⟨a, rfl⟩
    · rw [hq] at this; simp at this
  have hredq : ∀ i : Fin Γ.comps.length, Γ.Unpinned q → (Γ.comps[i].x = q ∨ Γ.comps[i].y = q) →
      Γ.toMG'.cls (.inl i) = some .minus → q = .inl 2 ∧ Γ.comps[i].y = q := by
    intro i hU hq hr
    have hk : Γ.comps[i].kind = .G .minus := by
      rw [hclsK i (by rw [hr]; simp)] at hr
      exact Local_mclass_minus hr
    exact Local_red_at hC (List.getElem_mem _) hk hU hq
  -- a crossing edge of `Γ` that is not red never satisfies the condition
  have hnr : ∀ i : Fin Γ.comps.length, Γ.toMG'.Crosses P (.inl i) →
      ¬ (Γ.Unpinned q ∧ (Γ.comps[i].x = q ∨ Γ.comps[i].y = q) ∧ B ∈ P') := by
    intro i hcr hcond
    have hc : Γ.toMG'.cls (.inl i) ≠ none := hcr.1
    have hr : Γ.toMG'.cls (.inl i) ≠ some .minus := hcr.2.1
    have hU : Γ.Unpinned q := hcond.1
    have hq : Γ.comps[i].x = q ∨ Γ.comps[i].y = q := hcond.2.1
    have hB : B ∈ P' := hcond.2.2
    obtain ⟨aq, hqa⟩ := hqL hU
    by_cases h2 : aq = 2
    · rw [hqa, h2] at hU hq
      have := (hminus hU i hq (by rw [← (hcomp i).1]; exact hc)).1
      apply hr
      rw [hclsK i hc, this]
      rfl
    · exact hnotB aq hqa hU (Local_pinClass_ne h2) hB
  -- the edge `.inl i` in `Γ'`, away from the condition
  have hcross : ∀ i : Fin Γ.comps.length, Γ.toMG'.cls (.inl i) ≠ none →
      Γ.toMG'.Cut P (.inl i) → ¬ (Γ.Unpinned q ∧ (Γ.comps[i].x = q ∨ Γ.comps[i].y = q) ∧ B ∈ P') →
      Γ'.toMG'.cls (.inl (ι i)) = Γ.toMG'.cls (.inl i) ∧
        Γ'.toMG'.IsVtx (Γ'.toMG'.ends (.inl (ι i))).1 ∧
        Γ'.toMG'.IsVtx (Γ'.toMG'.ends (.inl (ι i))).2 ∧ Γ'.toMG'.Cut P' (.inl (ι i)) := by
    intro i hc hcut hcond
    by_cases hat : Γ.Unpinned q ∧ (Γ.comps[i].x = q ∨ Γ.comps[i].y = q)
    · have hB : B ∉ P' := fun h => hcond ⟨hat.1, hat.2, h⟩
      obtain ⟨w, hwq, hends, hwP⟩ := hatq i hat.1 hat.2 hc hcut
      have hρw : Local_rho Γ' w = φ (Local_rho Γ w) := hρ w fun ⟨h, _⟩ => hwq h
      have hφw : φ (Local_rho Γ w) ∈ P' := (hmemP _ (Local_rho_vtx Γ w)).1 hwP
      have hne : B ≠ φ (Local_rho Γ w) := fun h => hB (h ▸ hφw)
      have hvw := hvtx' _ (Local_rho_vtx Γ w)
      have hvB : Γ'.toMG'.IsVtx B := by rw [← hρq]; exact Local_rho_vtx Γ' q
      have hcK := hclsK i hc
      rcases hends with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · have hc' : Γ'.toMG'.cls (.inl (ι i)) = Γ.comps[i].kind.mclass := by
          rw [(hcomp' i).1]
          show (if Γ.comps[i].kind = .dot ∨ Local_rho Γ' Γ.comps[i].x = Local_rho Γ' Γ.comps[i].y
            then none else _) = _
          rw [hx, hy, hρq, hρw, if_neg]
          rintro (h | h)
          · apply hc; rw [(hcomp i).1]; show (if _ then none else _) = none; rw [if_pos (Or.inl h)]
          · exact hne h
        have hc'' : Γ'.toMG'.cls (.inl (ι i)) ≠ none := by rw [hc', ← hcK]; exact hc
        have hen : Γ'.toMG'.ends (.inl (ι i)) = (B, φ (Local_rho Γ w)) := by
          rw [(hcomp' i).2 hc'']
          show (Local_rho Γ' Γ.comps[i].x, Local_rho Γ' Γ.comps[i].y) = _
          rw [hx, hy, hρq, hρw]
        refine ⟨by rw [hc', hcK], by rw [hen]; exact hvB, by rw [hen]; exact hvw, ?_⟩
        unfold MGraph.Cut
        rw [hen]
        exact Or.inr ⟨hB, hφw⟩
      · have hc' : Γ'.toMG'.cls (.inl (ι i)) = Γ.comps[i].kind.mclass := by
          rw [(hcomp' i).1]
          show (if Γ.comps[i].kind = .dot ∨ Local_rho Γ' Γ.comps[i].x = Local_rho Γ' Γ.comps[i].y
            then none else _) = _
          rw [hx, hy, hρq, hρw, if_neg]
          rintro (h | h)
          · apply hc; rw [(hcomp i).1]; show (if _ then none else _) = none; rw [if_pos (Or.inl h)]
          · exact hne h.symm
        have hc'' : Γ'.toMG'.cls (.inl (ι i)) ≠ none := by rw [hc', ← hcK]; exact hc
        have hen : Γ'.toMG'.ends (.inl (ι i)) = (φ (Local_rho Γ w), B) := by
          rw [(hcomp' i).2 hc'']
          show (Local_rho Γ' Γ.comps[i].x, Local_rho Γ' Γ.comps[i].y) = _
          rw [hx, hy, hρq, hρw]
        refine ⟨by rw [hc', hcK], by rw [hen]; exact hvw, by rw [hen]; exact hvB, ?_⟩
        unfold MGraph.Cut
        rw [hen]
        exact Or.inl ⟨hφw, hB⟩
    · exact hkeep i hc hcut hat
  -- the map of the edges
  classical
  let pinT : Fin Γ'.comps.length ⊕ Fin 3 := Local_pinT q
  let g : Fin Γ.comps.length ⊕ Fin 3 → Fin Γ'.comps.length ⊕ Fin 3 := fun e => match e with
    | .inl i => if Γ.Unpinned q ∧ (Γ.comps[i].x = q ∨ Γ.comps[i].y = q) ∧ B ∈ P' then pinT
      else .inl (ι i)
    | .inr a => .inr a
  have gl : ∀ i, ¬ (Γ.Unpinned q ∧ (Γ.comps[i].x = q ∨ Γ.comps[i].y = q) ∧ B ∈ P') →
      g (.inl i) = .inl (ι i) := fun i h => by simp only [g, if_neg h]
  have gp : ∀ i, (Γ.Unpinned q ∧ (Γ.comps[i].x = q ∨ Γ.comps[i].y = q) ∧ B ∈ P') →
      g (.inl i) = pinT := fun i h => by simp only [g, if_pos h]
  have hpinV : ∀ a, Γ.toMG'.cls (.inr a) ≠ none →
      Γ.toMG'.IsVtx (Γ.toMG'.ends (.inr a)).1 ∧ Γ.toMG'.IsVtx (Γ.toMG'.ends (.inr a)).2 := by
    intro a ha
    obtain ⟨c1, e1⟩ := Local_toMG'_pin Γ a
    rw [c1] at ha
    rw [e1]
    exact Local_pin_vok Γ a ha
  have pincross : ∀ a, Γ.toMG'.cls (.inr a) ≠ none → Γ.toMG'.Cut P (.inr a) →
      Γ'.toMG'.IsVtx (Γ'.toMG'.ends (.inr a)).1 ∧ Γ'.toMG'.IsVtx (Γ'.toMG'.ends (.inr a)).2 ∧
        Γ'.toMG'.Cut P' (.inr a) := by
    intro a ha hcut
    obtain ⟨v1, v2⟩ := hpinV a ha
    obtain ⟨-, he⟩ := hpin' a ha
    unfold MGraph.Cut at hcut ⊢
    rw [he]
    exact ⟨hvtx' _ v1, hvtx' _ v2, hcutφ _ _ v1 v2 hcut⟩
  have hpinU : ∀ a, Γ.toMG'.cls (.inr a) ≠ none → ¬ Γ.Unpinned (.inl a) := by
    intro a ha hU
    obtain ⟨c1, -⟩ := Local_toMG'_pin Γ a
    rw [c1] at ha
    apply ha
    simp [Local_pin, Local_anchor_none.2 hU.2]
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · rintro (i | a) hcr
    · rw [gl i (hnr i hcr)]
      obtain ⟨hc, hr, -, -, hcut⟩ := hcr
      obtain ⟨h1, h2, h3, h4⟩ := hcross i hc hcut (hnr i ⟨hc, hr, by
        rw [(hcomp i).2 hc]; exact Local_rho_vtx Γ _, by
        rw [(hcomp i).2 hc]; exact Local_rho_vtx Γ _, hcut⟩)
      exact ⟨by rw [h1]; exact hc, by rw [h1]; exact hr, h2, h3, h4⟩
    · obtain ⟨hc, hr, -, -, hcut⟩ := hcr
      obtain ⟨h1, -⟩ := hpin' a hc
      obtain ⟨v1, v2, hcut'⟩ := pincross a hc hcut
      exact ⟨by simp only [g]; rw [h1]; exact hc, by simp only [g]; rw [h1]; exact hr, v1, v2, hcut'⟩
  · rintro (i | a) (j | b) hci hcj hg
    · rw [gl i (hnr i hci), gl j (hnr j hcj)] at hg
      simp only [Sum.inl.injEq, ι, Fin.mk.injEq] at hg
      exact congrArg Sum.inl (Fin.ext hg)
    · rw [gl i (hnr i hci)] at hg
      simp [g] at hg
    · rw [gl j (hnr j hcj)] at hg
      simp [g] at hg
    · simpa [g] using hg
  · rintro (i | a) ⟨hr, v1, v2, hcut⟩
    · have hc : Γ.toMG'.cls (.inl i) ≠ none := by rw [hr]; simp
      by_cases hcond : Γ.Unpinned q ∧ (Γ.comps[i].x = q ∨ Γ.comps[i].y = q) ∧ B ∈ P'
      · rw [gp i hcond]
        obtain ⟨hq2, -⟩ := hredq i hcond.1 hcond.2.1 hr
        have hpT : pinT = .inr 2 := by
          show Local_pinT q = _
          rw [hq2]
          rfl
        obtain ⟨c1, e1⟩ := hpinq 2 hq2
        rw [hpT]
        refine ⟨by rw [c1]; rfl, ?_, ?_, ?_⟩
        · rw [e1]; rw [← hρq]; exact Local_rho_vtx Γ' _
        · rw [e1, hq2]; exact Or.inr (by rw [Local_mem_ext]; rfl)
        · unfold MGraph.Cut
          rw [e1, hq2]
          exact Or.inl ⟨hcond.2.2, fun h => Finset.disjoint_left.1 hdisj (hP' h)
            (by rw [Local_mem_ext]; rfl)⟩
      · rw [gl i hcond]
        obtain ⟨h1, h2, h3, h4⟩ := hcross i hc hcut hcond
        exact ⟨by rw [h1]; exact hr, h2, h3, h4⟩
    · have hc : Γ.toMG'.cls (.inr a) ≠ none := by rw [hr]; simp
      obtain ⟨h1, -⟩ := hpin' a hc
      obtain ⟨v1', v2', hcut'⟩ := pincross a hc hcut
      exact ⟨by simp only [g]; rw [h1]; exact hr, v1', v2', hcut'⟩
  · rintro (i | a) (j | b) ⟨ri, -⟩ ⟨rj, -⟩ hg
    · by_cases hi : Γ.Unpinned q ∧ (Γ.comps[i].x = q ∨ Γ.comps[i].y = q) ∧ B ∈ P' <;>
        by_cases hj : Γ.Unpinned q ∧ (Γ.comps[j].x = q ∨ Γ.comps[j].y = q) ∧ B ∈ P'
      · -- two red solid edges at the unpinned `⊖`
        by_contra hne
        have hij : i ≠ j := fun h => hne (by rw [h])
        obtain ⟨hq2, hyi⟩ := hredq i hi.1 hi.2.1 ri
        obtain ⟨-, hyj⟩ := hredq j hj.1 hj.2.1 rj
        rw [hq2] at hyi hyj
        have hdeg := (hE.2.2.2.1 (hq2 ▸ hi.1)).2
        unfold Graph.nonDotDeg at hdeg
        rw [← List.countP_eq_length_filter] at hdeg
        have hki : Γ.comps[i].kind = .G .minus := by
          have := hclsK i (by rw [ri]; simp)
          rw [ri] at this
          exact Local_mclass_minus this.symm
        have hkj : Γ.comps[j].kind = .G .minus := by
          have := hclsK j (by rw [rj]; simp)
          rw [rj] at this
          exact Local_mclass_minus this.symm
        have := Local_two_le_countP Γ.comps (fun c => decide ((c.x = .inl 2 ∨ c.y = .inl 2) ∧
          c.kind ≠ .dot ∧ c.kind ≠ .xdot)) i j hij
          (decide_eq_true ⟨Or.inr hyi, by rw [hki]; simp, by rw [hki]; simp⟩)
          (decide_eq_true ⟨Or.inr hyj, by rw [hkj]; simp, by rw [hkj]; simp⟩)
        omega
      · rw [gp i hi, gl j hj] at hg
        obtain ⟨hq2, -⟩ := hredq i hi.1 hi.2.1 ri
        have hpT : pinT = .inr 2 := by
          show Local_pinT q = _
          rw [hq2]
          rfl
        rw [hpT] at hg
        simp at hg
      · rw [gl i hi, gp j hj] at hg
        obtain ⟨hq2, -⟩ := hredq j hj.1 hj.2.1 rj
        have hpT : pinT = .inr 2 := by
          show Local_pinT q = _
          rw [hq2]
          rfl
        rw [hpT] at hg
        simp at hg
      · rw [gl i hi, gl j hj] at hg
        simp only [Sum.inl.injEq, ι, Fin.mk.injEq] at hg
        exact congrArg Sum.inl (Fin.ext hg)
    · have hca : Γ.toMG'.cls (.inr b) ≠ none := by rw [rj]; simp
      by_cases hi : Γ.Unpinned q ∧ (Γ.comps[i].x = q ∨ Γ.comps[i].y = q) ∧ B ∈ P'
      · rw [gp i hi] at hg
        obtain ⟨hq2, -⟩ := hredq i hi.1 hi.2.1 ri
        have hpT : pinT = .inr 2 := by
          show Local_pinT q = _
          rw [hq2]
          rfl
        rw [hpT] at hg
        simp only [g, Sum.inr.injEq] at hg
        rw [← hg] at hca
        exact absurd (hq2 ▸ hi.1) (hpinU 2 hca)
      · rw [gl i hi] at hg
        simp [g] at hg
    · have hca : Γ.toMG'.cls (.inr a) ≠ none := by rw [ri]; simp
      by_cases hj : Γ.Unpinned q ∧ (Γ.comps[j].x = q ∨ Γ.comps[j].y = q) ∧ B ∈ P'
      · rw [gp j hj] at hg
        obtain ⟨hq2, -⟩ := hredq j hj.1 hj.2.1 rj
        have hpT : pinT = .inr 2 := by
          show Local_pinT q = _
          rw [hq2]
          rfl
        rw [hpT] at hg
        simp only [g, Sum.inr.injEq] at hg
        rw [hg] at hca
        exact absurd (hq2 ▸ hj.1) (hpinU 2 hca)
      · rw [gl j hj] at hg
        simp [g] at hg
    · simpa [g] using hg

end AddPull

/-! ## `O_dot` -/

section ODot

variable {n : ℕ}

private theorem Local_dropX_fun (Γ : Graph 3 n) :
    (Local_dropX Γ).SameBlock = Γ.SameBlock ∧ (Local_dropX Γ).Unpinned = Γ.Unpinned ∧
      (Local_dropX Γ).flatAtom = Γ.flatAtom := by
  obtain ⟨hd, hm⟩ := Local_dropX_graphs Γ
  have := Local_graphs_fun hd hm
  exact ⟨this.1, this.2.2.2.2.2, this.2.2.2.2.1⟩

private theorem Local_mem_dropX {Γ : Graph 3 n} {c : Comp (Atom 3 n)} :
    c ∈ (Local_dropX Γ).comps ↔ c ∈ Γ.comps ∧ c.kind ≠ .xdot := by
  simp [Local_dropX, Local_nx]

private theorem Local_colour_dropX (Γ : Graph 3 n) :
    Γ.ColourInvB ↔ (Local_dropX Γ).ColourInvB := by
  rw [Local_colour_iff, Local_colour_iff]
  have hf := (Local_dropX_fun Γ).2.2
  constructor
  · intro h c hc
    have := h c (Local_mem_dropX.1 hc).1
    unfold Local_CC at this ⊢
    rw [hf]
    exact this
  · intro h c hc
    by_cases hx : c.kind = .xdot
    · unfold Local_CC
      simp [hx, Kind.isRandom]
    · have := h c (Local_mem_dropX.2 ⟨hc, hx⟩)
      unfold Local_CC at this ⊢
      rw [hf] at this
      exact this

private theorem Local_noGhost_dropX (Γ : Graph 3 n) : Γ.NoGhost ↔ (Local_dropX Γ).NoGhost := by
  constructor
  · intro h c hc
    exact h c (Local_mem_dropX.1 hc).1
  · intro h c hc
    by_cases hx : c.kind = .xdot
    · rw [hx]; simp
    · exact h c (Local_mem_dropX.2 ⟨hc, hx⟩)

private theorem Local_ext_dropX (Γ : Graph 3 n) :
    Γ.ExtClause ↔ (Local_dropX Γ).ExtClause ∧
      ∀ c ∈ Γ.comps, c.kind = .xdot → ¬ (Γ.Unpinned c.x ∧ Γ.Unpinned c.y) := by
  obtain ⟨hb, hu, -⟩ := Local_dropX_fun Γ
  have hdeg : ∀ u, (Local_dropX Γ).nonDotDeg u = Γ.nonDotDeg u := by
    intro u
    unfold Graph.nonDotDeg
    simp only [Local_dropX, List.filter_filter]
    congr 2
    funext c
    simp only [Local_nx]
    by_cases hx : c.kind = .xdot <;> simp [hx]
  have hdiffm : ∀ c, c.kind.isDiffusive = true → (c ∈ (Local_dropX Γ).comps ↔ c ∈ Γ.comps) := by
    intro c hd
    rw [Local_mem_dropX]
    exact ⟨fun h => h.1, fun h => ⟨h, by rintro hx; rw [hx] at hd; simp [Kind.isDiffusive] at hd⟩⟩
  have hhas : ∀ u, (Local_dropX Γ).HasDiffToPinned u ↔ Γ.HasDiffToPinned u := by
    intro u
    unfold Graph.HasDiffToPinned
    rw [hu]
    exact ⟨fun ⟨c, hc, hd, h⟩ => ⟨c, (hdiffm c hd).1 hc, hd, h⟩,
      fun ⟨c, hc, hd, h⟩ => ⟨c, (hdiffm c hd).2 hc, hd, h⟩⟩
  have hdt : ∀ u, (Local_dropX Γ).DiffToPinned u ↔ Γ.DiffToPinned u := by
    intro u
    unfold Graph.DiffToPinned
    rw [hu]
    exact ⟨fun h c hc hd => h c ((hdiffm c hd).2 hc) hd, fun h c hc hd => h c ((hdiffm c hd).1 hc) hd⟩
  have hdiffall : ∀ (P : Comp (Atom 3 n) → Prop), (∀ c ∈ (Local_dropX Γ).comps,
      c.kind.isDiffusive = true → P c) ↔ (∀ c ∈ Γ.comps, c.kind.isDiffusive = true → P c) :=
    fun P => ⟨fun h c hc hd => h c ((hdiffm c hd).2 hc) hd, fun h c hc hd => h c ((hdiffm c hd).1 hc) hd⟩
  have hblue : (∃ c ∈ (Local_dropX Γ).comps, c.kind = .G .plus ∧ (c.x = .inl 1 ∨ c.y = .inl 1)) ↔
      (∃ c ∈ Γ.comps, c.kind = .G .plus ∧ (c.x = .inl 1 ∨ c.y = .inl 1)) := by
    constructor
    · rintro ⟨c, hc, h⟩
      exact ⟨c, (Local_mem_dropX.1 hc).1, h⟩
    · rintro ⟨c, hc, h⟩
      exact ⟨c, Local_mem_dropX.2 ⟨hc, by rw [h.1]; simp⟩, h⟩
  have hx0 : ∀ c ∈ (Local_dropX Γ).comps, c.kind = .xdot →
      ¬ ((Local_dropX Γ).Unpinned c.x ∧ (Local_dropX Γ).Unpinned c.y) := by
    intro c hc hk
    exact absurd hk (Local_mem_dropX.1 hc).2
  unfold Graph.ExtClause
  rw [hb, hu, hdeg, hdeg, hhas, hhas, hdt, hdt,
    hdiffall (fun c => c.x ≠ .inl 2 ∧ c.y ≠ .inl 2), hblue]
  constructor
  · rintro ⟨e1, e2, e3, e4, e5⟩
    exact ⟨⟨e1, by rw [← hu]; exact hx0, e3, e4, e5⟩, e2⟩
  · rintro ⟨⟨e1, -, e3, e4, e5⟩, e2⟩
    exact ⟨e1, e2, e3, e4, e5⟩

/-- Graphs with the same components other than `×`-dotted edges, the new `×`-dotted edges not
between two unpinned atoms: carried by the identity, with the clauses kept. -/
private theorem Local_same3X_main {Γ Γ' : Graph 3 n} (h : Local_Same3X Γ Γ')
    (hX : ∀ c ∈ Γ'.comps, c.kind = .xdot → ¬ (Γ.Unpinned c.x ∧ Γ.Unpinned c.y))
    (hC : Γ.ColourInvB) (hE : Γ.ExtClause) (hG : Γ.NoGhost) :
    Local_Carry Γ.toMG' Γ'.toMG' id ∧ Γ'.ColourInvB ∧ Γ'.ExtClause ∧ Γ'.NoGhost ∧
      Γ'.molRep = Γ.molRep := by
  have h3 := Local_same3X_dropX h
  have e := Local_same3_clauses h3
  have hfun := Local_same3X_fun h
  refine ⟨Local_same3X_carry h, ?_, ?_, ?_, hfun.2.2.2.1⟩
  · rw [Local_colour_dropX] at hC ⊢
    exact e.1.2 hC
  · rw [Local_ext_dropX] at hE ⊢
    refine ⟨e.2.1.2 hE.1, fun c hc hk => ?_⟩
    rw [hfun.2.2.2.2.2]
    exact hX c hc hk
  · rw [Local_noGhost_dropX] at hG ⊢
    exact e.2.2.2 hG

/-- The atom `u` lies in a block with an internal atom. -/
private def Local_anch {k : ℕ} (Γ : Graph k n) (u : Atom k n) : Prop := ∃ b : Fin n, Γ.SameBlock u (.inr b)

/-- The invariant carried by the local expansions: sequentially pre-deterministic in the block
reading, the charge pattern of the block normal form, the clause on the external atoms, no ghost
edge. -/
private def Local_Inv (Γ : Graph 3 n) : Prop :=
  spdPM' Γ ∧ Γ.ColourInvB ∧ Γ.ExtClause ∧ Γ.NoGhost

/-- Every label atom lies in the molecule `v`. -/
private def Local_LabAt {k : ℕ} (Γ : Graph k n) (v : Atom k n) : Prop :=
  ∀ c ∈ Γ.comps, ∀ pq u, c.label = some (pq, u) → Γ.molRep u = v

/-- The dotted edge `p = q` and `q = p` give the same molecular graph and clauses. -/
private theorem Local_dotrev (Γ : Graph 3 n) (p q : Atom 3 n) :
    Local_Carry (Local_addG Γ q p).toMG' (Local_addG Γ p q).toMG' id ∧
      ((Local_addG Γ q p).ColourInvB → (Local_addG Γ p q).ColourInvB) ∧
      ((Local_addG Γ q p).ExtClause → (Local_addG Γ p q).ExtClause) ∧
      ((Local_addG Γ q p).NoGhost → (Local_addG Γ p q).NoGhost) ∧
      (Local_addG Γ p q).molRep = (Local_addG Γ q p).molRep := by
  have hd : (Local_addG Γ p q).dotGraph = (Local_addG Γ q p).dotGraph := by
    ext u v
    have h1 := Local_fromRel_add (fun c => c.kind = .dot) Γ.comps (mkC .dot p q) rfl u v
    have h2 := Local_fromRel_add (fun c => c.kind = .dot) Γ.comps (mkC .dot q p) rfl u v
    simp only [Graph.dotGraph, Local_addG] at h1 h2 ⊢
    rw [h1, h2]
    simp only [mkC]
    tauto
  have hm : (Local_addG Γ p q).molGraph = (Local_addG Γ q p).molGraph := by
    ext u v
    have h1 := Local_fromRel_add (fun c => c.kind.joinsMol = true) Γ.comps (mkC .dot p q) rfl u v
    have h2 := Local_fromRel_add (fun c => c.kind.joinsMol = true) Γ.comps (mkC .dot q p) rfl u v
    simp only [Graph.molGraph, Local_addG] at h1 h2 ⊢
    rw [h1, h2]
    simp only [mkC]
    tauto
  have hfun := Local_graphs_fun hd hm
  have hr := Local_graphs_rho hd hm
  have hint : (Local_addG Γ p q).toMG'.int = (Local_addG Γ q p).toMG'.int := by
    simp only [Graph.toMG', hfun.2.2.2.1]
  have hsame : List.Forall₂ Local_Same ((Local_addG Γ q p).comps.map (Local_rd (Local_addG Γ q p)))
      ((Local_addG Γ p q).comps.map (Local_rd (Local_addG Γ p q))) := by
    rw [hr.2.1]
    simp only [Local_addG, List.map_append, List.map_cons, List.map_nil]
    refine List.rel_append (List.forall₂_same.2 fun e _ => Local_Same.refl e)
      (List.Forall₂.cons (Or.inl ⟨by simp [Local_rd, mkC], by simp [Local_rd, mkC]⟩) List.Forall₂.nil)
  refine ⟨?_, ?_, ?_, ?_, hfun.2.2.2.1⟩
  · refine Local_carry_trans_id (Local_carry_toRG _) (Local_carry_trans_id ?_
      (Local_carry_ofRG _))
    unfold Local_RG
    rw [hint, hr.2.2]
    exact Local_ELG_same hsame (fun a => Local_Same.refl _) (Local_rdL_vok _ _) (Local_pin_vok _)
  · rw [Local_colour_iff, Local_colour_iff]
    intro h c hc
    rcases List.mem_append.1 hc with hc | hc
    · have := h c (List.mem_append_left _ hc)
      unfold Local_CC at this ⊢
      rw [hfun.2.2.2.2.1]
      exact this
    · rw [List.mem_singleton] at hc
      subst hc
      simp [Local_CC, mkC, Kind.isRandom]
  · intro h
    obtain ⟨E1, E2, E3, E4, E5⟩ := h
    have hu := hfun.2.2.2.2.2
    have hb := hfun.1
    have hdeg : ∀ u, (Local_addG Γ p q).nonDotDeg u = (Local_addG Γ q p).nonDotDeg u := by
      intro u
      simp [Graph.nonDotDeg, Local_addG, List.filter_append, mkC]
    have hmem : ∀ c, c.kind ≠ .dot → (c ∈ (Local_addG Γ p q).comps ↔ c ∈ (Local_addG Γ q p).comps) := by
      intro c hk
      simp only [Local_addG, List.mem_append, List.mem_singleton]
      constructor
      · rintro (h | rfl)
        · exact Or.inl h
        · simp [mkC] at hk
      · rintro (h | rfl)
        · exact Or.inl h
        · simp [mkC] at hk
    have hdk : ∀ κ : Kind, κ.isDiffusive = true → κ ≠ .dot := by rintro κ h rfl; simp [Kind.isDiffusive] at h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hb]; exact E1
    · intro c hc hk
      rw [hu]
      exact E2 c ((hmem c (by rw [hk]; simp)).1 hc) hk
    · rw [hu]
      intro hU
      obtain ⟨⟨c, hc, hd, hor⟩, hdt⟩ := E3 hU
      refine ⟨⟨c, (hmem c (hdk _ hd)).2 hc, hd, by rw [hu]; exact hor⟩, fun c hc hd => ?_⟩
      rw [hu]
      exact hdt c ((hmem c (hdk _ hd)).1 hc) hd
    · rw [hu, hdeg]
      intro hU
      obtain ⟨a1, a2⟩ := E4 hU
      exact ⟨fun c hc hd => a1 c ((hmem c (hdk _ hd)).1 hc) hd, a2⟩
    · rw [hu, hdeg]
      intro hU
      obtain ⟨a1, a2, a3⟩ := E5 hU
      refine ⟨?_, fun c hc hd => ?_, a3⟩
      · rcases a1 with ⟨c, hc, hk, h⟩ | ⟨c, hc, hd, hor⟩
        · exact Or.inl ⟨c, (hmem c (by rw [hk]; simp)).2 hc, hk, h⟩
        · exact Or.inr ⟨c, (hmem c (hdk _ hd)).2 hc, hd, by rw [hu]; exact hor⟩
      · rw [hu]
        exact a2 c ((hmem c (hdk _ hd)).1 hc) hd
  · intro h c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact h c (List.mem_append_left _ hc)
    · rw [List.mem_singleton] at hc
      subst hc
      simp [mkC]

/-- One dotted edge `p = q` added, `p` or `q` in a block with an internal atom: the invariant is
kept and the isolated subsets are read back. -/
private theorem Local_addDot_main {Γ : Graph 3 n} {p q : Atom 3 n} (hI : Local_Inv Γ)
    (ha : Local_anch Γ p ∨ Local_anch Γ q) :
    Local_Inv (Local_addG Γ p q) ∧
      Local_Pull Γ.toMG' (Local_addG Γ p q).toMG' (Local_addG Γ p q).molRep := by
  obtain ⟨hs, hC, hE, hG⟩ := hI
  rcases ha with ⟨b, hb⟩ | ⟨b, hb⟩
  · obtain ⟨h1, h2, h3, h4⟩ := spdPM'_addDot n Γ p q hs hC hE hG ⟨b, hb⟩
    exact ⟨⟨h1, h2, h3, h4⟩, Local_add_pull hb hC hE hG hs h1⟩
  · obtain ⟨h1, h2, h3, h4⟩ := spdPM'_addDot n Γ q p hs hC hE hG ⟨b, hb⟩
    have hpull := Local_add_pull hb hC hE hG hs h1
    obtain ⟨c1, c2, c3, c4, c5⟩ := Local_dotrev Γ p q
    obtain ⟨s', -, -, p'⟩ := c1 (Graph.toMG'_disjoint _) (Graph.toMG'_noGhost _ h4) h1
    refine ⟨⟨s', c2 h2, c3 h3, c4 h4⟩, ?_⟩
    rw [c5]
    exact Local_pull_trans hpull p'

/-- The dotted edges `p.1 = p.2.1` for the pairs `p` of `L` added one at a time. -/
private def Local_addDs (Γ : Graph 3 n) (L : List (Atom 3 n × Atom 3 n × Bool)) : Graph 3 n :=
  L.foldl (fun Δ p => Local_addG Δ p.1 p.2.1) Γ

private theorem Local_addDs_comps (Γ : Graph 3 n) (L : List (Atom 3 n × Atom 3 n × Bool)) :
    (Local_addDs Γ L).comps = Γ.comps ++ L.map (fun p => mkC .dot p.1 p.2.1) ∧
      (Local_addDs Γ L).coeff = Γ.coeff := by
  induction L generalizing Γ with
  | nil => simp [Local_addDs]
  | cons p L ih =>
    obtain ⟨h1, h2⟩ := ih (Local_addG Γ p.1 p.2.1)
    refine ⟨?_, h2⟩
    change (Local_addDs (Local_addG Γ p.1 p.2.1) L).comps = _
    rw [h1]
    simp [Local_addG]

private theorem Local_anch_add {Γ : Graph 3 n} {p q u : Atom 3 n} (h : Local_anch Γ u) :
    Local_anch (Local_addG Γ p q) u := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, Local_add_sameBlock_mono hb⟩

private theorem Local_labAt_add {Γ : Graph 3 n} {p q v : Atom 3 n} (h : Local_LabAt Γ v) :
    Local_LabAt (Local_addG Γ p q) ((Local_addG Γ p q).molRep v) := by
  intro c hc pq u hl
  rcases List.mem_append.1 hc with hc | hc
  · rw [← h c hc pq u hl, Local_add_molRep_molRep]
  · rw [List.mem_singleton] at hc
    subst hc
    simp [mkC] at hl

/-- The dotted edges of a list of pairs, each with an atom in a block with an internal atom, added
one at a time. -/
private theorem Local_addDs_main : ∀ (L : List (Atom 3 n × Atom 3 n × Bool)) (Γ : Graph 3 n),
    Local_Inv Γ → (∀ p ∈ L, Local_anch Γ p.1 ∨ Local_anch Γ p.2.1) →
    Local_Inv (Local_addDs Γ L) ∧ ∃ φ, Local_Pull Γ.toMG' (Local_addDs Γ L).toMG' φ ∧
      (∀ v, φ (Γ.molRep v) = (Local_addDs Γ L).molRep v) ∧
      (∀ v, Local_LabAt Γ v → Local_LabAt (Local_addDs Γ L) ((Local_addDs Γ L).molRep v)) ∧
      (∀ u v, Γ.SameBlock u v → (Local_addDs Γ L).SameBlock u v)
  | [], Γ, hI, _ => by
    refine ⟨hI, id, Local_pull_id _, fun v => rfl, fun v h => ?_, fun u v h => h⟩
    intro c hc pq u hl
    have e := h c hc pq u hl
    change Γ.molRep u = Γ.molRep v
    rw [← e, Local_molRep_idem]
  | p :: L, Γ, hI, hL => by
    obtain ⟨hI₁, hp₁⟩ := Local_addDot_main (p := p.1) (q := p.2.1) hI (hL p List.mem_cons_self)
    have hL' : ∀ p' ∈ L, Local_anch (Local_addG Γ p.1 p.2.1) p'.1 ∨
        Local_anch (Local_addG Γ p.1 p.2.1) p'.2.1 := by
      intro p' hp'
      rcases hL p' (List.mem_cons_of_mem _ hp') with h | h
      · exact Or.inl (Local_anch_add h)
      · exact Or.inr (Local_anch_add h)
    obtain ⟨hI₂, φ, hpull, hφ, hlab, hsb⟩ := Local_addDs_main L _ hI₁ hL'
    refine ⟨hI₂, φ ∘ (Local_addG Γ p.1 p.2.1).molRep, Local_pull_trans hp₁ hpull,
      fun v => ?_, fun v h => ?_, fun u v h => hsb u v (Local_add_sameBlock_mono h)⟩
    · change φ ((Local_addG Γ p.1 p.2.1).molRep (Γ.molRep v)) = _
      rw [Local_add_molRep_molRep]
      exact hφ v
    · have := hlab _ (Local_labAt_add (p := p.1) (q := p.2.1) h)
      show Local_LabAt (Local_addDs (Local_addG Γ p.1 p.2.1) L)
        ((Local_addDs (Local_addG Γ p.1 p.2.1) L).molRep v)
      have e : (Local_addDs (Local_addG Γ p.1 p.2.1) L).molRep
          ((Local_addG Γ p.1 p.2.1).molRep v) =
          (Local_addDs (Local_addG Γ p.1 p.2.1) L).molRep v := by
        rw [← hφ, ← hφ, Local_molRep_idem]
      rw [← e]
      exact this

/-- The pairs of `Graph.splitPairs`: joined by a solid edge (flag `true`) or by a `×`-dotted
edge (flag `false`). -/
private theorem Local_sp_mem {Γ : Graph 3 n} {p : Atom 3 n × Atom 3 n × Bool}
    (h : p ∈ Γ.splitPairs) :
    (p.2.2 = true → ∃ c ∈ Γ.comps, c.kind.isSolid = true ∧
      (c.x = p.1 ∧ c.y = p.2.1 ∨ c.x = p.2.1 ∧ c.y = p.1)) ∧
    (p.2.2 = false → ∃ c ∈ Γ.comps, c.kind = .xdot ∧
      (c.x = p.1 ∧ c.y = p.2.1 ∨ c.x = p.2.1 ∧ c.y = p.1)) := by
  unfold Graph.splitPairs at h
  simp only [List.mem_filterMap] at h
  obtain ⟨q, -, hq⟩ := h
  split_ifs at hq with hs
  obtain rfl := Option.some.inj hq
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · simp only at h1
    rw [List.any_eq_true] at h1
    obtain ⟨c, hc, hb⟩ := h1
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hb
    exact ⟨c, hc, hb.1, hb.2⟩
  · simp only at h1
    rw [h1] at hs
    have h2 : (Γ.comps.any fun c => (c.kind == .xdot) && ((c.x == q.1 && c.y == q.2) ||
        (c.x == q.2 && c.y == q.1))) = true := by
      by_contra hn
      simp only [Bool.not_eq_true] at hn
      rw [hn] at hs
      simp at hs
    rw [List.any_eq_true] at h2
    obtain ⟨c, hc, hb⟩ := h2
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hb
    exact ⟨c, hc, hb.1, hb.2⟩

private theorem Local_anch_of_not_unpinned {Γ : Graph 3 n} {u : Atom 3 n} (h : ¬ Γ.Unpinned u) :
    Local_anch Γ u := by
  cases u with
  | inr b => exact ⟨b, SimpleGraph.Reachable.refl _⟩
  | inl a =>
    by_contra hn
    exact h ⟨rfl, fun b hb => hn ⟨b, hb⟩⟩

private theorem Local_not_unpinned_of_anch {Γ : Graph 3 n} {u : Atom 3 n} (h : Local_anch Γ u) :
    ¬ Γ.Unpinned u := fun hU => by
  obtain ⟨b, hb⟩ := h
  exact hU.2 b hb

/-- One atom of every pair of `Graph.splitPairs` lies in a block with an internal atom. -/
private theorem Local_sp_anch {Γ : Graph 3 n} (hC : Γ.ColourInvB) (hE : Γ.ExtClause)
    {p : Atom 3 n × Atom 3 n × Bool} (h : p ∈ Γ.splitPairs) :
    Local_anch Γ p.1 ∨ Local_anch Γ p.2.1 := by
  obtain ⟨h1, h2⟩ := Local_sp_mem h
  cases hb : p.2.2 with
  | true =>
    obtain ⟨c, hc, hs, hor⟩ := h1 hb
    have hx := Local_colour_x hC hc (Local_solid_kinds hs).2.2.1
    have hxa : Local_anch Γ c.x := by
      obtain ⟨b, hb'⟩ : ∃ b, Γ.flatAtom c.x = .inr b := by
        rcases hf : Γ.flatAtom c.x with a | b
        · rw [hf] at hx; simp at hx
        · exact ⟨b, rfl⟩
      exact ⟨b, hb' ▸ Local_flat_block Γ c.x⟩
    rcases hor with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl (h ▸ hxa)
    · exact Or.inr (h ▸ hxa)
  | false =>
    obtain ⟨c, hc, hk, hor⟩ := h2 hb
    have := hE.2.1 c hc hk
    rcases not_and_or.1 this with h | h
    · rcases hor with ⟨h', -⟩ | ⟨h', -⟩
      · exact Or.inl (h' ▸ Local_anch_of_not_unpinned h)
      · exact Or.inr (h' ▸ Local_anch_of_not_unpinned h)
    · rcases hor with ⟨-, h'⟩ | ⟨-, h'⟩
      · exact Or.inr (h' ▸ Local_anch_of_not_unpinned h)
      · exact Or.inl (h' ▸ Local_anch_of_not_unpinned h)

/-- The pairs of `SP` without solid edge joined by a `×`-dotted edge. -/
private def Local_xonly (SP : List (Atom 3 n × Atom 3 n × Bool)) (u v : Atom 3 n) : Bool :=
  SP.any fun p => !p.2.2 && ((p.1 == u && p.2.1 == v) || (p.1 == v && p.2.1 == u))

/-- The components kept by `Graph.dotChoice`. -/
private def Local_kept (Γ : Graph 3 n) (SP : List (Atom 3 n × Atom 3 n × Bool)) :
    List (Comp (Atom 3 n)) :=
  Γ.comps.filter fun c => !(c.kind == .xdot && Local_xonly SP c.x c.y)

/-- The components added by `Graph.dotChoice`. -/
private def Local_added (SP A : List (Atom 3 n × Atom 3 n × Bool)) : List (Comp (Atom 3 n)) :=
  SP.filterMap fun p =>
    if p ∈ A then some (mkC .dot p.1 p.2.1) else if p.2.2 then some (mkC .xdot p.1 p.2.1) else none

/-- The `×`-dotted edges added by `Graph.dotChoice`. -/
private def Local_addedX (SP A : List (Atom 3 n × Atom 3 n × Bool)) : List (Comp (Atom 3 n)) :=
  SP.filterMap fun p => if p ∈ A then none else if p.2.2 then some (mkC .xdot p.1 p.2.1) else none

private theorem Local_dotChoice_comps (Γ : Graph 3 n) (SP A : List (Atom 3 n × Atom 3 n × Bool)) :
    (Γ.dotChoice SP A).comps = Local_kept Γ SP ++ Local_added SP A := rfl

private theorem Local_added_perm (SP A : List (Atom 3 n × Atom 3 n × Bool)) :
    (Local_added SP A).Perm (Local_addedX SP A ++
      (SP.filter fun p => decide (p ∈ A)).map (fun p => mkC .dot p.1 p.2.1)) := by
  induction SP with
  | nil => simp [Local_added, Local_addedX]
  | cons p SP ih =>
    unfold Local_added Local_addedX at *
    by_cases hA : p ∈ A
    · simp only [List.filterMap_cons, hA, if_true, List.filter_cons, decide_true,
        List.map_cons]
      exact (ih.cons _).trans List.perm_middle.symm
    · by_cases h2 : p.2.2 = true
      · simp only [List.filterMap_cons, hA, if_false, h2, List.filter_cons, decide_false,
          Bool.false_eq_true]
        exact ih.cons _
      · simp only [List.filterMap_cons, hA, if_false, h2, List.filter_cons, decide_false,
          Bool.false_eq_true]
        exact ih

/-- A term `t` of an expansion of `Γ` at the atom `x` keeps the invariant, maps `x` to an internal
atom, reads its isolated subsets back in `Γ` with the molecule of `x` sent to that of its image,
and keeps the labels in the molecule of `x`. -/
private def Local_Good (Γ : Graph 3 n) (x : Atom 3 n) (t : Tracked 3 n) : Prop :=
  Local_Inv t.g ∧ (t.f x).isRight = true ∧ ∃ φ, Local_Pull Γ.toMG' t.g.toMG' φ ∧
    φ (Γ.molRep x) = t.g.molRep (t.f x) ∧
    (Local_LabAt Γ (Γ.molRep x) → Local_LabAt t.g (t.g.molRep (t.f x)))

private theorem Local_good_self {Γ : Graph 3 n} (hI : Local_Inv Γ) (x : Atom 3 n)
    (hx : x.isRight = true) : Local_Good Γ x (Tracked.self Γ) :=
  ⟨hI, hx, id, Local_pull_id _, rfl, id⟩

set_option maxHeartbeats 2000000 in
/-- **[II, Lemma 5.10] for `O_dot`** in the block reading, with the isolated subsets: every term of
`O_dot` of a graph with the invariant is good. -/
private theorem Local_oDot_good {Γ : Graph 3 n} (hI : Local_Inv Γ) (x : Atom 3 n)
    (hx : x.isRight = true) : ∀ t ∈ oDotT Γ, Local_Good Γ x t := by
  intro t ht
  unfold oDotT at ht
  dsimp only at ht
  split_ifs at ht with h1 h2
  · rw [List.mem_singleton] at ht
    subst ht
    exact Local_good_self hI x hx
  · rw [List.mem_singleton] at ht
    subst ht
    exact Local_good_self hI x hx
  obtain ⟨A, -, hm⟩ := List.mem_filterMap.1 ht
  obtain ⟨hs, hC, hE, hG⟩ := hI
  set SP := Γ.splitPairs with hSP
  -- the `×`-dotted edges changed
  set Γ₂ : Graph 3 n := ⟨Local_kept Γ SP ++ Local_addedX SP A, Γ.coeff⟩ with hΓ₂
  have hX2 : ∀ c ∈ Local_addedX SP A, c.kind = .xdot ∧ ∃ p ∈ SP, p.2.2 = true ∧
      c.x = p.1 ∧ c.y = p.2.1 := by
    intro c hc
    unfold Local_addedX at hc
    obtain ⟨p, hp, hpc⟩ := List.mem_filterMap.1 hc
    split_ifs at hpc with ha hb
    obtain rfl := Option.some.inj hpc
    exact ⟨rfl, p, hp, hb, rfl, rfl⟩
  have h3X : Local_Same3X Γ Γ₂ := by
    unfold Local_Same3X
    have e : Γ₂.comps.filter Local_nx = Γ.comps.filter Local_nx := by
      simp only [hΓ₂, List.filter_append, Local_kept, List.filter_filter]
      have e2 : (Local_addedX SP A).filter Local_nx = [] := by
        rw [List.filter_eq_nil_iff]
        intro c hc
        simp [Local_nx, (hX2 c hc).1]
      rw [e2, List.append_nil]
      congr 1
      funext c
      by_cases hk : c.kind = .xdot <;> simp [Local_nx, hk]
    rw [e]
  have hXok : ∀ c ∈ Γ₂.comps, c.kind = .xdot → ¬ (Γ.Unpinned c.x ∧ Γ.Unpinned c.y) := by
    intro c hc hk
    rcases List.mem_append.1 hc with hc | hc
    · exact hE.2.1 c (List.mem_filter.1 hc).1 hk
    · obtain ⟨-, p, hp, -, hx', hy'⟩ := hX2 c hc
      rw [hx', hy']
      rcases Local_sp_anch hC hE hp with h | h
      · exact fun ⟨a, _⟩ => Local_not_unpinned_of_anch h a
      · exact fun ⟨_, b⟩ => Local_not_unpinned_of_anch h b
  obtain ⟨c2, hC2, hE2, hG2, hr2⟩ := Local_same3X_main h3X hXok hC hE hG
  obtain ⟨hs2, -, -, hp2⟩ := c2 (Graph.toMG'_disjoint _) (Graph.toMG'_noGhost _ hG) hs
  have hb2 := (Local_same3X_fun h3X).1
  -- the dotted edges added
  set LA := SP.filter fun p => decide (p ∈ A) with hLA
  have hLA : ∀ p ∈ LA, Local_anch Γ₂ p.1 ∨ Local_anch Γ₂ p.2.1 := by
    intro p hp
    have hp' := (List.mem_filter.1 hp).1
    unfold Local_anch
    rw [hb2]
    exact Local_sp_anch hC hE hp'
  obtain ⟨hI3, φ3, hp3, hφ3, hlab3, -⟩ := Local_addDs_main LA Γ₂ ⟨hs2, hC2, hE2, hG2⟩ hLA
  set Γ₃ := Local_addDs Γ₂ LA with hΓ₃
  -- `Γ₃` is the dotted edge choice up to order
  set D := Γ.dotChoice SP A with hD
  have h3 : Local_Same3 Γ₃ D := by
    unfold Local_Same3
    rw [hD, Local_dotChoice_comps, (Local_addDs_comps Γ₂ LA).1]
    refine List.Perm.map _ ?_
    simp only [hΓ₂, List.append_assoc]
    exact List.Perm.append_left _ (Local_added_perm SP A)
  obtain ⟨hs3, hC3, hE3, hG3⟩ := hI3
  have e3 := Local_same3_clauses h3
  obtain ⟨hsD, -, -, hpD⟩ := Local_same3_carry h3 (Graph.toMG'_disjoint _)
    (Graph.toMG'_noGhost _ hG3) hs3
  have hCD : D.ColourInvB := e3.1.2 hC3
  have hED : D.ExtClause := e3.2.1.2 hE3
  have hGD : D.NoGhost := e3.2.2.2 hG3
  have hrD := (Local_same3_fun h3).2.2.2.1
  -- `O_merge`
  obtain ⟨hst, -, -, hpt⟩ := Local_merge_carry hm hED.1 (Graph.toMG'_disjoint _)
    (Graph.toMG'_noGhost _ hGD) hsD
  obtain ⟨hCt, hEt, hGt⟩ := Local_merge_clauses hm hCD hED hGD
  refine ⟨⟨hst, hCt, hEt, hGt⟩, ?_, _, Local_pull_trans hp2 (Local_pull_trans hp3
    (Local_pull_trans hpD hpt)), ?_, ?_⟩
  · rw [Local_merge_f_int hm]
    exact hx
  · simp only [Function.comp, id]
    rw [← hr2, hφ3, ← hrD, Local_merge_molRep hm]
  · intro hl
    refine Local_merge_labAt hm x ?_
    have hl2 : Local_LabAt Γ₂ (Γ₂.molRep x) := by
      intro c hc pq u hlu
      rw [hr2]
      rcases List.mem_append.1 hc with hc | hc
      · exact hl c (List.mem_filter.1 hc).1 pq u hlu
      · obtain ⟨-, p, -, -, -, -⟩ := hX2 c hc
        unfold Local_addedX at hc
        obtain ⟨p', -, hpc⟩ := List.mem_filterMap.1 hc
        split_ifs at hpc
        obtain rfl := Option.some.inj hpc
        simp [mkC] at hlu
    have hl3 := hlab3 _ hl2
    intro c hc pq u hlu
    have hc3 : c ∈ Γ₃.comps := by
      have := (Local_same3_ex h3 (fun _ _ _ => True))
      have hmem : c ∈ D.comps := hc
      rw [hD, Local_dotChoice_comps] at hmem
      rw [(Local_addDs_comps Γ₂ LA).1]
      have hp : (Local_kept Γ SP ++ Local_added SP A).Perm (Γ₂.comps ++
          LA.map fun p => mkC .dot p.1 p.2.1) := by
        simp only [hΓ₂, List.append_assoc]
        exact List.Perm.append_left _ (Local_added_perm SP A)
      exact hp.subset hmem
    rw [hrD, hl3 c hc3 pq u hlu]
    rw [← hφ3, ← hφ3, Local_molRep_idem]

end ODot

/-! ## Lists of components -/

section CompLists

variable {k n : ℕ}

private theorem Local_liftCs_append (j : ℕ) (l l' : List (Comp (Atom k n))) :
    liftCs j (l ++ l') = liftCs j l ++ liftCs j l' := by
  simp [liftCs]

private theorem Local_strip_liftCs (j : ℕ) (l : List (Comp (Atom k n))) :
    (liftCs j l).map Local_stripC = liftCs j (l.map Local_stripC) := by
  simp [liftCs, Local_stripC, Comp.map, Function.comp_def]

private theorem Local_strip_labelQs (u : Atom k n) (l : List (Comp (Atom k n))) :
    (labelQs u l).map Local_stripC = l.map Local_stripC := by
  simp only [labelQs, List.map_map]
  congr 1
  funext c
  simp only [Function.comp, Comp.labelQ, Local_stripC]
  split_ifs <;> rfl

private theorem Local_strip_mkC (κ : Kind) (a b : Atom k n) : Local_stripC (mkC κ a b) = mkC κ a b :=
  rfl

private theorem Local_strip_solidC (ch : Charge) (a b : Atom k n) :
    Local_stripC (solidC ch a b) = solidC ch a b := by
  unfold solidC
  split_ifs <;> rfl

private theorem Local_strip_labelFree {Γ : Graph k n} (h : Γ.LabelFree) :
    Γ.comps.map Local_stripC = Γ.comps := by
  conv_rhs => rw [← List.map_id Γ.comps]
  refine List.map_congr_left fun c hc => ?_
  obtain ⟨κ, a, b, m, l⟩ := c
  simp only [Local_stripC, id]
  have := h _ hc
  simp only at this
  rw [this]

private theorem Local_liftA_zero (u : Atom k n) : liftA 0 u = u := by
  cases u <;> rfl

private theorem Local_liftCs_zero (l : List (Comp (Atom k n))) : liftCs 0 l = l := by
  unfold liftCs
  conv_rhs => rw [← List.map_id l]
  refine List.map_congr_left fun c _ => ?_
  obtain ⟨κ, a, b, m, lab⟩ := c
  simp only [Comp.map, Local_liftA_zero, id]
  congr 1
  · conv_rhs => rw [← List.map_id m]
    exact List.map_congr_left fun u _ => Local_liftA_zero u
  · cases lab with
    | none => rfl
    | some q => obtain ⟨q1, q2⟩ := q; simp [Prod.map, Local_liftA_zero]

private theorem Local_proj_zero (x : Fin n) (u : Atom k (n + 0)) : Local_proj 0 x u = u := by
  rcases u with a | i
  · rfl
  · simp [Local_proj, i.2]

private theorem Local_comp_proj_zero (x : Fin n) (c : Comp (Atom k (n + 0))) :
    c.map (Local_proj 0 x) = c := by
  obtain ⟨κ, a, b, m, l⟩ := c
  simp only [Comp.map, Local_proj_zero]
  congr 1
  · conv_rhs => rw [← List.map_id m]
    exact List.map_congr_left fun u _ => Local_proj_zero x u
  · cases l with
    | none => rfl
    | some q => obtain ⟨q1, q2⟩ := q; simp [Prod.map, Local_proj_zero]

private theorem Local_eraseIdx_perm {α : Type*} (l : List α) (i : ℕ) (hi : i < l.length) :
    l.Perm (l.eraseIdx i ++ [l[i]]) := by
  rw [List.eraseIdx_eq_take_drop_succ]
  conv_lhs => rw [← List.take_append_drop i l, ← List.getElem_cons_drop hi]
  simp only [List.append_assoc]
  exact List.Perm.append_left _ (List.perm_append_singleton _ _).symm

private theorem Local_dTerms_mem {V : Type*} [DecidableEq V] {p q : V} {cs : List (Comp V)}
    {d : List (Comp V)} (h : d ∈ dTerms p q cs) :
    ∃ (i : ℕ) (hi : i < cs.length) (ps : List (Comp V)), cs[i].dPieces p q = some ps ∧
      d = cs.eraseIdx i ++ ps := by
  unfold dTerms at h
  obtain ⟨i, -, hd⟩ := List.mem_filterMap.1 h
  obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.1 hd
  exact ⟨i, i.2, ps, hps, rfl⟩

private theorem Local_liftCs_eraseIdx (j : ℕ) (l : List (Comp (Atom k n))) (i : ℕ) :
    liftCs j (l.eraseIdx i) = (liftCs j l).eraseIdx i := by
  unfold liftCs
  rw [List.eraseIdx_map]

private theorem Local_liftCs_get (j : ℕ) (l : List (Comp (Atom k n))) (i : ℕ)
    (hi : i < (liftCs j l).length) :
    (liftCs j l)[i] = (l[i]'(by simpa [liftCs] using hi)).map (liftA j) := by
  simp [liftCs]

private theorem Local_reach_comp {Γ : Graph k n} {c : Comp (Atom k n)} (hc : c ∈ Γ.comps)
    (hk : c.kind.joinsMol = true) : Γ.molGraph.Reachable c.x c.y := by
  by_cases h : c.x = c.y
  · rw [h]
  · exact SimpleGraph.Adj.reachable (by
      simp only [Graph.molGraph, SimpleGraph.fromRel_adj]
      exact ⟨h, Or.inl ⟨c, hc, hk, rfl, rfl⟩⟩)

private theorem Local_eraseIdxs_pick_perm {α : Type*} (S : List ℕ) (l : List α) :
    l.Perm (eraseIdxs S l ++ pickIdxs S l) := by
  unfold eraseIdxs pickIdxs
  have h := (List.filter_append_perm (fun p : α × ℕ => !S.contains p.2) l.zipIdx).map Prod.fst
  rw [List.map_append] at h
  simp only [Bool.not_not] at h
  have e2 : l.zipIdx.map Prod.fst = l := by simp
  rw [e2] at h
  exact h.symm

private theorem Local_mem_eraseIdxs {α : Type*} {S : List ℕ} {l : List α} {a : α}
    (h : a ∈ eraseIdxs S l) : a ∈ l := by
  unfold eraseIdxs at h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  exact List.fst_mem_of_mem_zipIdx (List.mem_filter.1 hp).1

private theorem Local_mem_pickIdxs {α : Type*} {S : List ℕ} {l : List α} {a : α}
    (h : a ∈ pickIdxs S l) : a ∈ l := by
  unfold pickIdxs at h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  exact List.fst_mem_of_mem_zipIdx (List.mem_filter.1 hp).1

/-- The entries of `List.zipIdx` with a given index. -/
private theorem Local_zipIdx_eq {α : Type*} : ∀ (l : List α) (s i : ℕ) (h1 : s ≤ i)
    (h2 : i < s + l.length),
    (l.zipIdx s).filter (fun p => p.2 == i) = [(l[i - s]'(by omega), i)]
  | [], s, i, h1, h2 => by simp at h2; omega
  | a :: l, s, i, h1, h2 => by
    rw [List.zipIdx_cons, List.filter_cons]
    by_cases hs : s = i
    · subst hs
      have hnil : (l.zipIdx (s + 1)).filter (fun p => p.2 == s) = [] := by
        rw [List.filter_eq_nil_iff]
        intro p hp
        obtain ⟨q, k⟩ := p
        have := (List.mem_zipIdx hp).1
        simp only [beq_iff_eq]
        omega
      rw [if_pos (by simp), hnil]
      simp
    · have hne : ¬ (s == i) = true := by simpa using hs
      rw [if_neg hne]
      have ih := Local_zipIdx_eq l (s + 1) i (by omega) (by simp at h2; omega)
      rw [ih]
      congr 2
      have : i - s = (i - (s + 1)) + 1 := by omega
      simp only [this, List.getElem_cons_succ]

/-- The entry at a position of `S` separated from the other entries at positions of `S`. -/
private theorem Local_pick_split {α : Type*} (S : List ℕ) (l : List α) (i : ℕ) (hi : i < l.length)
    (hiS : i ∈ S) : (pickIdxs S l).Perm (pickIdxs (S.filter (· != i)) l ++ [l[i]]) := by
  unfold pickIdxs
  have h := (List.filter_append_perm (fun p : α × ℕ => p.2 != i)
    (l.zipIdx.filter fun p => S.contains p.2)).map Prod.fst
  rw [List.map_append, List.filter_filter, List.filter_filter] at h
  have e1 : (l.zipIdx.filter fun p => (p.2 != i) && S.contains p.2) =
      l.zipIdx.filter fun p => (S.filter (· != i)).contains p.2 := by
    congr 1
    funext p
    by_cases h1 : p.2 = i <;> simp [h1]
  have e2 : ((l.zipIdx.filter fun p => !(p.2 != i) && S.contains p.2).map Prod.fst) = [l[i]] := by
    have e3 : (l.zipIdx.filter fun p => !(p.2 != i) && S.contains p.2) =
        l.zipIdx.filter fun p => p.2 == i := by
      congr 1
      funext p
      by_cases h1 : p.2 = i
      · simp [h1, hiS]
      · rw [show (p.2 != i) = true by simp [h1], show (p.2 == i) = false by simp [h1]]
        rfl
    rw [e3, Local_zipIdx_eq l 0 i (by omega) (by omega)]
    simp
  rw [e1, e2] at h
  exact h.symm

/-- Two entries at distinct positions separated from the others. -/
private theorem Local_eraseIdxs2_perm {α : Type*} (l : List α) (i j : ℕ) (hi : i < l.length)
    (hj : j < l.length) (hij : i ≠ j) : l.Perm (eraseIdxs [i, j] l ++ [l[i], l[j]]) := by
  refine (Local_eraseIdxs_pick_perm [i, j] l).trans (List.Perm.append_left _ ?_)
  have e : ([i, j].filter (· != j)) = [i] := by simp [hij]
  have A : (pickIdxs [i, j] l).Perm (pickIdxs [i] l ++ [l[j]]) := by
    have := Local_pick_split [i, j] l j hj (by simp)
    rwa [e] at this
  have e' : ([i].filter (· != i)) = [] := by simp
  have hnil : pickIdxs ([] : List ℕ) l = [] := by
    unfold pickIdxs
    simp
  have B : (pickIdxs [i] l).Perm [l[i]] := by
    have := Local_pick_split [i] l i hi (by simp)
    rw [e', hnil] at this
    simpa using this
  exact A.trans (List.Perm.append_right _ B)

end CompLists

/-! ## Composition of the steps -/

section Compose

variable {n : ℕ}

/-- Good terms compose along `TExpansion.bind`. -/
private theorem Local_good_bind {Γ : Graph 3 n} {x : Atom 3 n} {E : TExpansion 3 n}
    {O : ∀ {n' : ℕ}, (Atom 3 n → Atom 3 n') → Graph 3 n' → TExpansion 3 n'}
    (hE : ∀ t ∈ E, Local_Good Γ x t)
    (hO : ∀ t ∈ E, ∀ s ∈ O t.f t.g, Local_Good t.g (t.f x) s) :
    ∀ u ∈ E.bind O, Local_Good Γ x u := by
  intro u hu
  unfold TExpansion.bind at hu
  obtain ⟨t, ht, hu⟩ := List.mem_flatMap.1 hu
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hu
  obtain ⟨-, -, φ, hp, hφ, hl⟩ := hE t ht
  obtain ⟨hI, hx, ψ, hq, hψ, hl'⟩ := hO t ht s hs
  refine ⟨hI, hx, ψ ∘ φ, Local_pull_trans hp hq, ?_, fun h => hl' (by rw [← hφ] at *; exact hl h)⟩
  simp only [Function.comp]
  rw [hφ, hψ]

/-- A new component of a waved, light, weight or solid kind between internal atoms read in the
molecule of `x`. -/
private theorem Local_newOK_gen {Γ : Graph 3 n} {x : Fin n} {j : ℕ} (c : Comp (Atom 3 (n + j)))
    (hk : (∃ w, c.kind = .waved w) ∨ (∃ ch, c.kind = .light ch) ∨ (∃ ch, c.kind = .weight ch) ∨
      (∃ ch, c.kind = .G ch))
    (hu : c.x.isRight = true) (hv : c.y.isRight = true)
    (hxu : Γ.SameMol (Local_proj j x c.x) (.inr x)) (hxv : Γ.SameMol (Local_proj j x c.y) (.inr x)) :
    Local_NewOK Γ x j c := by
  have hρ : Local_rho Γ (Local_proj j x c.x) = Local_rho Γ (Local_proj j x c.y) := by
    rw [Local_rho_molx hxu, Local_rho_molx hxv]
  refine ⟨hu, hv, ?_, ?_, ?_, ?_, ?_, fun _ => ⟨hxu, hxv⟩⟩
  · rcases hk with ⟨w, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ <;> rw [h] <;> simp
  · rcases hk with ⟨w, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ <;> rw [h] <;> simp
  · rcases hk with ⟨w, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ <;> rw [h] <;> simp
  · rcases hk with ⟨w, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ | ⟨ch, h⟩ <;> rw [h] <;> simp [Kind.isDiffusive]
  · simp only [Local_rd, Comp.map, hρ, or_true, if_true]

/-- The two factors of `-∂_{h_{pq}}` of a lifted random component, at internal atoms `p`, `q` read
in the molecule of `x`, form a path of `Local_PathOK`. -/
private theorem Local_pathOK_dPieces {Γ : Graph 3 n} {x : Fin n} {j : ℕ} (c : Comp (Atom 3 n))
    {p q : Atom 3 (n + j)} {ps : List (Comp (Atom 3 (n + j)))}
    (h : (c.map (liftA j)).dPieces p q = some ps) (hp : p.isRight = true) (hq : q.isRight = true)
    (hxp : Γ.SameMol (Local_proj j x p) (.inr x)) (hxq : Γ.SameMol (Local_proj j x q) (.inr x)) :
    Local_PathOK Γ x j [c] ps := by
  right
  have hb : (if (c.map (liftA j)).kind.isWeight then (c.map (liftA j)).x else (c.map (liftA j)).y) =
      liftA j (if c.kind.isWeight then c.x else c.y) := by
    by_cases hw : c.kind.isWeight = true <;> simp [Comp.map, hw]
  unfold Comp.dPieces at h
  simp only at h
  rw [hb] at h
  split at h
  all_goals first
    | (obtain rfl := Option.some.inj h
       rename_i hk
       exact ⟨c, .plus, p, q, rfl, by simp only [Comp.map] at hk; simp [hk], hp, hq, hxp, hxq,
         List.Perm.refl _⟩)
    | (obtain rfl := Option.some.inj h
       rename_i hk
       exact ⟨c, .minus, q, p, rfl, by simp only [Comp.map] at hk; simp [hk], hq, hp, hxq, hxp,
         List.Perm.refl _⟩)
    | simp at h

/-- A term of `Local_Dec` whose label atoms are read in the molecule of `x` is good. -/
private theorem Local_good_of_dec {Γ : Graph 3 n} (hI : Local_Inv Γ) {x : Fin n} {j : ℕ}
    {t : Tracked 3 n} (hn : t.nOut = n + j) (hf : ∀ u, t.f u = hn ▸ liftA j u)
    (hd : Local_Dec Γ x j (hn ▸ t.g))
    (hl : Local_LabAt Γ (Γ.molRep (.inr x)) →
      ∀ c ∈ (hn ▸ t.g : Graph 3 (n + j)).comps, ∀ pq u, c.label = some (pq, u) →
        Γ.SameMol (Local_proj j x u) (.inr x)) :
    Local_Good Γ (.inr x) t := by
  obtain ⟨tn, tg, tf⟩ := t
  simp only at hn
  subst hn
  simp only at hf hd hl
  obtain ⟨hs, hC, hE, hG⟩ := hI
  obtain ⟨hc, hC', hE', hG'⟩ := Local_dec_main hd hC hE hG
  obtain ⟨hs', -, -, hp⟩ := hc (Graph.toMG'_disjoint _) (Graph.toMG'_noGhost _ hG) hs
  have hfx : tf (.inr x) = liftA j (.inr x) := hf _
  refine ⟨⟨hs', hC', hE', hG'⟩, by show (tf (.inr x)).isRight = true; rw [hfx]; rfl, liftA j, hp,
    ?_, fun hlab => ?_⟩
  · show liftA j (Γ.molRep (.inr x)) = tg.molRep (tf (.inr x))
    rw [hfx, Local_dec_molRep hd, Local_proj_lift]
  · intro c hc pq u hlu
    show tg.molRep u = tg.molRep (tf (.inr x))
    rw [hfx, Local_dec_molRep hd, Local_dec_molRep hd, Local_proj_lift]
    congr 1
    exact (Local_molRep_eq_iff _ _ _).2 (hl hlab c hc pq u hlu)

/-- The splitting of the regular weights on `x`: some kept, some changed into light weights, the
others removed. -/
private theorem Local_splitRegular_dec (x : Atom 3 n) : ∀ (cs : List (Comp (Atom 3 n))),
    ∀ p ∈ splitRegular x cs, ∃ K D R D' : List (Comp (Atom 3 n)),
      cs.Perm (K ++ D ++ R) ∧ p.1.Perm (K ++ D') ∧
      List.Forall₂ (fun c c' => ∃ ch, c.kind = .weight ch ∧ c.x = x ∧ c.label = none ∧
        c' = { c with kind := .light ch }) D D' ∧
      ∀ c ∈ R, (∃ ch, c.kind = .weight ch) ∧ c.x = x ∧ c.label = none
  | [], p, hp => by
    simp only [splitRegular, List.mem_singleton] at hp
    subst hp
    exact ⟨[], [], [], [], by simp, by simp, List.Forall₂.nil, by simp⟩
  | c :: cs, p, hp => by
    have ih := Local_splitRegular_dec x cs
    unfold splitRegular at hp
    split at hp
    · rename_i ch hk
      split_ifs at hp with hc
      · rcases List.mem_append.1 hp with hp | hp
        · obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
          obtain ⟨K, D, R, D', h1, h2, h3, h4⟩ := ih p₀ hp₀
          refine ⟨K, D, c :: R, D', ?_, h2, h3, ?_⟩
          · refine (h1.cons c).trans ?_
            have := (List.perm_middle (l₁ := K ++ D) (l₂ := R) (a := c)).symm
            simpa [List.append_assoc] using this
          · intro c' hc'
            rcases List.mem_cons.1 hc' with rfl | hc'
            · exact ⟨⟨ch, hk⟩, hc.1, by simpa using hc.2⟩
            · exact h4 c' hc'
        · obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
          obtain ⟨K, D, R, D', h1, h2, h3, h4⟩ := ih p₀ hp₀
          refine ⟨K, c :: D, R, { c with kind := .light ch } :: D', ?_, ?_,
            List.Forall₂.cons ⟨ch, hk, hc.1, by simpa using hc.2, rfl⟩ h3, h4⟩
          · have e : K ++ D ++ R = K ++ (D ++ R) := List.append_assoc _ _ _
            rw [e] at h1
            have := (h1.cons c).trans (List.perm_middle (l₁ := K) (l₂ := D ++ R) (a := c)).symm
            simpa [List.append_assoc] using this
          · exact (h2.cons _).trans List.perm_middle.symm
      · obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
        obtain ⟨K, D, R, D', h1, h2, h3, h4⟩ := ih p₀ hp₀
        exact ⟨c :: K, D, R, D', h1.cons c, h2.cons c, h3, h4⟩
    · obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.1 hp
      obtain ⟨K, D, R, D', h1, h2, h3, h4⟩ := ih p₀ hp₀
      exact ⟨c :: K, D, R, D', h1.cons c, h2.cons c, h3, h4⟩

/-- **The first step of `O_weight`**: the terms of `O^{(x),1}_weight` are good. -/
private theorem Local_oWeight1_good {Γ : Graph 3 n} (hI : Local_Inv Γ) (x : Fin n) :
    ∀ t ∈ oWeight1T (.inr x) Γ, Local_Good Γ (.inr x) t := by
  intro t ht
  unfold oWeight1T at ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  obtain ⟨K, D, R, D', h1, h2, h3, h4⟩ := Local_splitRegular_dec (.inr x) Γ.comps p hp
  refine Local_good_of_dec (j := 0) hI rfl (fun u => (Local_liftA_zero u).symm) ?_ ?_
  · refine ⟨K.map Local_stripC, D.map Local_stripC, [], R.map Local_stripC,
      D'.map Local_stripC, [], [], ?_, ?_, ?_, Or.inl ⟨rfl, rfl⟩, ?_, by simp, fun i => i.elim0⟩
    · have := h1.map Local_stripC
      simpa [List.map_append] using this
    · rw [Local_liftCs_zero]
      have := (h2.map Local_stripC).symm
      simpa [List.map_append] using this
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine h3.imp fun d d' ⟨ch, hk, hx, hl, hd'⟩ => ?_
      subst hd'
      refine ⟨Or.inr ⟨by simp [Local_stripC, hk, Kind.isWeight], by simp [Local_stripC,
        Kind.isWeight]⟩, by simp [Local_stripC, hk, Kind.isRandom],
        Or.inl (Local_liftA_zero _).symm, Or.inl (Local_liftA_zero _).symm, ?_⟩
      unfold Local_SameR
      rw [Local_comp_proj_zero]
      left
      refine ⟨?_, ?_⟩ <;> simp [Local_rd, Local_stripC, hk, Kind.mclass]
    · intro c hc
      obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
      obtain ⟨⟨ch, hk⟩, -, -⟩ := h4 c₀ hc₀
      simp [Local_stripC, hk, Kind.isWeight]
  · intro hlab c hc pq u hlu
    rw [Local_proj_zero]
    have hc' : c ∈ K ++ D' := h2.subset hc
    rcases List.mem_append.1 hc' with hc' | hc'
    · have := hlab c (h1.symm.subset (List.mem_append_left _ (List.mem_append_left _ hc'))) pq u hlu
      exact (Local_molRep_eq_iff _ _ _).1 this
    · obtain ⟨d, -, ⟨ch, -, -, hl, rfl⟩⟩ := Local_f2_right h3 hc'
      simp [hl] at hlu

end Compose

/-! ## The terms of the local expansions -/

section Terms

variable {n : ℕ}

/-- `Local_Dec` without replaced components. -/
private theorem Local_dec_noD {Γ : Graph 3 n} {x : Fin n} {j : ℕ} {Γ' : Graph 3 (n + j)}
    (K P R : List (Comp (Atom 3 n))) (P' N : List (Comp (Atom 3 (n + j))))
    (h1 : (Γ.comps.map Local_stripC).Perm (K ++ P ++ R))
    (h2 : (liftCs j K ++ P' ++ N).Perm (Γ'.comps.map Local_stripC))
    (h4 : Local_PathOK Γ x j P P') (h5 : ∀ c ∈ R, c.kind.isWeight = true)
    (h6 : ∀ c ∈ N, Local_NewOK Γ x j c)
    (h7 : ∀ i : Fin j, Γ'.molGraph.Reachable (newA i) (liftA j (.inr x))) :
    Local_Dec Γ x j Γ' :=
  ⟨K, [], P, R, [], P', N, by simpa using h1, by simpa using h2, List.Forall₂.nil, h4, h5, h6, h7⟩

/-- The old atom `x` and the new atoms: internal and read in the molecule of `x`. -/
private def Local_AtX (x : Fin n) {j : ℕ} (u : Atom 3 (n + j)) : Prop :=
  u = liftA j (.inr x) ∨ ∃ i : Fin j, u = newA i

private theorem Local_atX {Γ : Graph 3 n} {x : Fin n} {j : ℕ} {u : Atom 3 (n + j)}
    (h : Local_AtX x u) : u.isRight = true ∧ Γ.SameMol (Local_proj j x u) (.inr x) := by
  rcases h with rfl | ⟨i, rfl⟩
  · exact ⟨rfl, by rw [Local_proj_lift]; exact Or.inl rfl⟩
  · exact ⟨rfl, by rw [Local_proj_new]; exact Or.inl rfl⟩

/-- A new component `mkC κ a b` at the atom `x` and the new atoms. -/
private theorem Local_newOK_mkC {Γ : Graph 3 n} {x : Fin n} {j : ℕ} (κ : Kind)
    (hk : (∃ w, κ = .waved w) ∨ (∃ ch, κ = .light ch) ∨ (∃ ch, κ = .weight ch) ∨
      (∃ ch, κ = .G ch)) {a b : Atom 3 (n + j)} (ha : Local_AtX x a) (hb : Local_AtX x b) :
    Local_NewOK Γ x j (mkC κ a b) :=
  Local_newOK_gen (Γ := Γ) _ hk (Local_atX (Γ := Γ) ha).1 (Local_atX (Γ := Γ) hb).1
    (Local_atX ha).2 (Local_atX hb).2

private theorem Local_m3_1 {Γ' : Graph 3 (n + 1)} {x : Fin n} {w : Wave}
    (h : mkC (.waved w) (liftA 1 (.inr x)) (newA 0) ∈ Γ'.comps) :
    ∀ i : Fin 1, Γ'.molGraph.Reachable (newA i) (liftA 1 (.inr x)) := by
  intro i
  obtain rfl : i = 0 := Fin.fin_one_eq_zero i
  exact (Local_reach_comp h rfl).symm

private theorem Local_m3_2 {Γ' : Graph 3 (n + 2)} {x : Fin n} {w w' : Wave}
    (h1 : mkC (.waved w) (liftA 2 (.inr x)) (newA 0) ∈ Γ'.comps)
    (h2 : mkC (.waved w') (newA 0) (newA 1) ∈ Γ'.comps) :
    ∀ i : Fin 2, Γ'.molGraph.Reachable (newA i) (liftA 2 (.inr x)) := by
  intro i
  have r1 : Γ'.molGraph.Reachable (newA 0) (liftA 2 (.inr x)) := (Local_reach_comp h1 rfl).symm
  match i with
  | 0 => exact r1
  | 1 => exact (Local_reach_comp h2 rfl).symm.trans r1

/-- A term of an expansion of `Δ` at `x` with `j` new atoms, of the form of `Local_Dec`, whose
labels lie in the molecule of `x`. -/
private def Local_DecT (Δ : Graph 3 n) (x : Fin n) (t : Tracked 3 n) : Prop :=
  ∃ (j : ℕ) (hn : t.nOut = n + j), (∀ u, t.f u = hn ▸ liftA j u) ∧ Local_Dec Δ x j (hn ▸ t.g) ∧
    ∀ c ∈ (hn ▸ t.g : Graph 3 (n + j)).comps, ∀ pq u, c.label = some (pq, u) →
      Δ.SameMol (Local_proj j x u) (.inr x)

private theorem Local_good_of_decT {Δ : Graph 3 n} (hI : Local_Inv Δ) {x : Fin n}
    {t : Tracked 3 n} (h : Local_DecT Δ x t) : Local_Good Δ (.inr x) t := by
  obtain ⟨j, hn, hf, hd, hl⟩ := h
  exact Local_good_of_dec hI hn hf hd fun _ => hl

/-- The construction of `Local_DecT` for a term `⟨cs, d⟩` with `j` new atoms. -/
private theorem Local_decT_mk {Δ : Graph 3 n} {x : Fin n} (j : ℕ)
    (cs : List (Comp (Atom 3 (n + j)))) (d : Coeff)
    (K P R : List (Comp (Atom 3 n))) (P' N : List (Comp (Atom 3 (n + j))))
    (h1 : (Δ.comps.map Local_stripC).Perm (K ++ P ++ R))
    (h2 : (liftCs j K ++ P' ++ N).Perm (cs.map Local_stripC))
    (h4 : Local_PathOK Δ x j P P') (h5 : ∀ c ∈ R, c.kind.isWeight = true)
    (h6 : ∀ c ∈ N, Local_NewOK Δ x j c)
    (h7 : ∀ i : Fin j, (⟨cs, d⟩ : Graph 3 (n + j)).molGraph.Reachable (newA i) (liftA j (.inr x)))
    (hl : ∀ c ∈ cs, ∀ pq u, c.label = some (pq, u) → Local_AtX x u) :
    Local_DecT Δ x ⟨n + j, ⟨cs, d⟩, liftA j⟩ :=
  ⟨j, rfl, fun _ => rfl, Local_dec_noD K P R P' N h1 h2 h4 h5 h6 h7,
    fun c hc pq u hlu => (Local_atX (Γ := Δ) (hl c hc pq u hlu)).2⟩

private theorem Local_label_liftCs {j : ℕ} {l : List (Comp (Atom 3 n))}
    (hl : ∀ c ∈ l, c.label = none) : ∀ c ∈ liftCs j l, c.label = none := by
  intro c hc
  obtain ⟨c₀, hc₀, rfl⟩ := Local_mem_liftCs.1 hc
  simp [Comp.map, hl c₀ hc₀]

private theorem Local_label_labelQs {V : Type} {u : V} {l : List (Comp V)}
    (hl : ∀ c ∈ l, c.label = none) : ∀ c ∈ labelQs u l, ∀ pq w, c.label = some (pq, w) → w = u := by
  intro c hc pq w hw
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  unfold Comp.labelQ at hw
  split_ifs at hw
  · simp only [Option.some.injEq, Prod.mk.injEq] at hw
    exact hw.2.symm
  · rw [hl c₀ hc₀] at hw
    simp at hw

private theorem Local_mem_labelQs_nr {V : Type} {u : V} {l : List (Comp V)} {c : Comp V}
    (hc : c ∈ l) (hr : c.kind.isRandom = false) : c ∈ labelQs u l := by
  refine List.mem_map.2 ⟨c, hc, ?_⟩
  simp [Comp.labelQ, hr]

private theorem Local_label_solidC {V : Type} [DecidableEq V] (ch : Charge) (a b : V) :
    (solidC ch a b).label = none := by
  unfold solidC
  split_ifs <;> rfl

private theorem Local_label_dPieces {V : Type} [DecidableEq V] {p q : V} {c : Comp V}
    {ps : List (Comp V)} (h : c.dPieces p q = some ps) : ∀ c' ∈ ps, c'.label = none := by
  unfold Comp.dPieces at h
  simp only at h
  generalize (if c.kind.isWeight = true then c.x else c.y) = b at h
  split at h
  all_goals first
    | (obtain rfl := Option.some.inj h
       intro c' hc'
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
       rcases hc' with rfl | rfl <;> exact Local_label_solidC _ _ _)
    | simp at h

private theorem Local_strip_dPieces {V : Type} [DecidableEq V] {p q : V} {c : Comp V}
    {ps : List (Comp V)} (h : c.dPieces p q = some ps) : ps.map Local_stripC = ps := by
  conv_rhs => rw [← List.map_id ps]
  refine List.map_congr_left fun c' hc' => ?_
  obtain ⟨κ, a, b, m, l⟩ := c'
  have := Local_label_dPieces h _ hc'
  simp only at this
  simp [Local_stripC, this]

/-- The construction of `Local_DecT` for a term `⟨cs, d⟩` without new atoms. -/
private theorem Local_decT_mk0 {Δ : Graph 3 n} {x : Fin n} (cs : List (Comp (Atom 3 n))) (d : Coeff)
    (h : (cs.map Local_stripC).Perm (Δ.comps.map Local_stripC))
    (hl : ∀ c ∈ cs, ∀ pq u, c.label = some (pq, u) → u = .inr x) :
    Local_DecT Δ x ⟨n, ⟨cs, d⟩, id⟩ := by
  refine ⟨0, rfl, fun u => (Local_liftA_zero u).symm, Local_dec_noD (Δ.comps.map Local_stripC) [] []
    [] [] (by simp) ?_ (Or.inl ⟨rfl, rfl⟩) (by simp) (by simp) (fun i => i.elim0),
    fun c hc pq u hlu => ?_⟩
  · rw [Local_liftCs_zero]
    simpa using h.symm
  · have := hl c hc pq u hlu
    rw [this, Local_proj_zero]
    exact Or.inl rfl

/-- A term of `dTerms` of a lifted list. -/
private theorem Local_dTerms_lift {j : ℕ} {f : List (Comp (Atom 3 n))} {p q : Atom 3 (n + j)}
    {d : List (Comp (Atom 3 (n + j)))} (h : d ∈ dTerms p q (liftCs j f)) :
    ∃ (i : ℕ) (hi : i < f.length) (ps : List (Comp (Atom 3 (n + j)))),
      (f[i].map (liftA j)).dPieces p q = some ps ∧ d = liftCs j (f.eraseIdx i) ++ ps ∧
      f.Perm (f.eraseIdx i ++ [f[i]]) := by
  obtain ⟨i, hi, ps, hps, rfl⟩ := Local_dTerms_mem h
  have hi' : i < f.length := by simpa [liftCs] using hi
  refine ⟨i, hi', ps, ?_, by rw [Local_liftCs_eraseIdx], Local_eraseIdx_perm f i hi'⟩
  rw [← Local_liftCs_get]
  exact hps

/-- **The light weight expansion**: the terms of [I, (3.5)] at an internal atom `x` of a graph
without labels have the form of `Local_Dec`. -/
private theorem Local_oW2_decT {Δ : Graph 3 n} (hlf : Δ.LabelFree) (x : Fin n)
    {E : TExpansion 3 n} (hE : oWeight2Pos (.inr x) Δ = some E) : ∀ t ∈ E, Local_DecT Δ x t := by
  unfold oWeight2Pos at hE
  split at hE
  · simp at hE
  rename_i i hi
  dsimp only at hE
  obtain rfl := Option.some.inj hE
  obtain ⟨hilt, hli, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
  have hli' : Δ.comps[i].kind = .light .plus := by
    simp only [Bool.and_eq_true, beq_iff_eq] at hli
    exact hli.1
  set f := Δ.comps.eraseIdx i with hf
  have hsΔ : Δ.comps.map Local_stripC = Δ.comps := Local_strip_labelFree hlf
  have hflf : ∀ c ∈ f, c.label = none := fun c hc => hlf c (List.mem_of_mem_eraseIdx hc)
  have hsf : f.map Local_stripC = f := Local_strip_labelFree (Γ := ⟨f, 0⟩) hflf
  have hperm : Δ.comps.Perm (f ++ [Δ.comps[i]]) := Local_eraseIdx_perm _ _ hilt
  have hR : ∀ c ∈ [Δ.comps[i]], c.kind.isWeight = true := by
    intro c hc
    rw [List.mem_singleton] at hc
    rw [hc, hli']
    rfl
  have hx1 : Local_AtX x (liftA 1 (.inr x) : Atom 3 (n + 1)) := Or.inl rfl
  have ha1 : Local_AtX x (newA 0 : Atom 3 (n + 1)) := Or.inr ⟨0, rfl⟩
  have hx2 : Local_AtX x (liftA 2 (.inr x) : Atom 3 (n + 2)) := Or.inl rfl
  have ha2 : Local_AtX x (newA 0 : Atom 3 (n + 2)) := Or.inr ⟨0, rfl⟩
  have hb2 : Local_AtX x (newA 1 : Atom 3 (n + 2)) := Or.inr ⟨1, rfl⟩
  have kW : ∀ w, ((∃ w', Kind.waved w = .waved w') ∨ (∃ ch, Kind.waved w = .light ch) ∨
      (∃ ch, Kind.waved w = .weight ch) ∨ (∃ ch, Kind.waved w = .G ch)) := fun w => Or.inl ⟨w, rfl⟩
  have kL : ∀ c, ((∃ w', Kind.light c = .waved w') ∨ (∃ ch, Kind.light c = .light ch) ∨
      (∃ ch, Kind.light c = .weight ch) ∨ (∃ ch, Kind.light c = .G ch)) :=
    fun c => Or.inr (Or.inl ⟨c, rfl⟩)
  have kWt : ∀ c, ((∃ w', Kind.weight c = .waved w') ∨ (∃ ch, Kind.weight c = .light ch) ∨
      (∃ ch, Kind.weight c = .weight ch) ∨ (∃ ch, Kind.weight c = .G ch)) :=
    fun c => Or.inr (Or.inr (Or.inl ⟨c, rfl⟩))
  have kG : ∀ c, ((∃ w', Kind.G c = .waved w') ∨ (∃ ch, Kind.G c = .light ch) ∨
      (∃ ch, Kind.G c = .weight ch) ∨ (∃ ch, Kind.G c = .G ch)) :=
    fun c => Or.inr (Or.inr (Or.inr ⟨c, rfl⟩))
  intro t ht
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at ht
  rcases ht with ((((((rfl | rfl) | ⟨d, hd, rfl⟩) | ⟨d, hd, rfl⟩) | (rfl | rfl | rfl | rfl)) |
    ⟨d, hd, rfl⟩) | ⟨d, hd, rfl⟩)
  · -- `m s_{xα} (G_{xx} - m)(G_{αα} - m) f`
    refine Local_decT_mk 1 _ _ Δ.comps [] [] [] [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0),
      mkC (.light .plus) (newA 0) (newA 0)] (by rw [hsΔ]; simp) ?_ (Or.inl ⟨rfl, rfl⟩) (by simp)
      ?_ (Local_m3_1 (w := .s) (by simp)) ?_
    · simp [List.map_append, Local_strip_liftCs, hsΔ, Local_strip_mkC]
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact Local_newOK_mkC _ (kW _) hx1 ha1
      · exact Local_newOK_mkC _ (kL _) ha1 ha1
    · intro c hc pq u hlu
      exfalso
      rcases List.mem_append.1 hc with hc | hc
      · rw [Local_label_liftCs (fun c hc => hlf c hc) c hc] at hlu; simp at hlu
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp [mkC] at hlu
  · -- `m S⁺_{xα} s_{αβ} (G_{αα} - m)(G_{ββ} - m) f`
    refine Local_decT_mk 2 _ _ f [] [Δ.comps[i]] [] [mkC (.waved .plus) (liftA 2 (.inr x)) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0),
      mkC (.light .plus) (newA 1) (newA 1)] (by rw [hsΔ]; simpa using hperm) ?_
      (Or.inl ⟨rfl, rfl⟩) hR ?_ (Local_m3_2 (w := .plus) (w' := .s) (by simp) (by simp)) ?_
    · simp [List.map_append, Local_strip_liftCs, hsf, Local_strip_mkC]
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact Local_newOK_mkC _ (kW _) hx2 ha2
      · exact Local_newOK_mkC _ (kW _) ha2 hb2
      · exact Local_newOK_mkC _ (kL _) ha2 ha2
      · exact Local_newOK_mkC _ (kL _) hb2 hb2
    · intro c hc pq u hlu
      exfalso
      rcases List.mem_append.1 hc with hc | hc
      · rw [Local_label_liftCs hflf c hc] at hlu; simp at hlu
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> simp [mkC] at hlu
  · -- the derivative terms with one new atom
    obtain ⟨i', hi', ps, hps, rfl, hpf⟩ := Local_dTerms_lift hd
    refine Local_decT_mk 1 _ _ (f.eraseIdx i') [f[i']] [Δ.comps[i]] ps
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 (.inr x))]
      (by rw [hsΔ]; exact hperm.trans (List.Perm.append_right _ hpf)) ?_
      (Local_pathOK_dPieces _ hps rfl rfl (Local_atX ha1).2 (Local_atX hx1).2) hR ?_
      (Local_m3_1 (w := .s) (by simp)) ?_
    · have hs' : (f.eraseIdx i').map Local_stripC = f.eraseIdx i' :=
        Local_strip_labelFree (Γ := ⟨_, 0⟩) fun c hc => hflf c (List.mem_of_mem_eraseIdx hc)
      simp [List.map_append, Local_strip_liftCs, hs', Local_strip_dPieces hps, Local_strip_mkC]
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact Local_newOK_mkC _ (kW _) hx1 ha1
      · exact Local_newOK_mkC _ (kG _) ha1 hx1
    · intro c hc pq u hlu
      exfalso
      simp only [List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · rw [Local_label_liftCs (fun c hc => hflf c (List.mem_of_mem_eraseIdx hc)) c hc] at hlu
        simp at hlu
      · rw [Local_label_dPieces hps c hc] at hlu; simp at hlu
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp [mkC] at hlu
  · -- the derivative terms with two new atoms
    obtain ⟨i', hi', ps, hps, rfl, hpf⟩ := Local_dTerms_lift hd
    refine Local_decT_mk 2 _ _ (f.eraseIdx i') [f[i']] [Δ.comps[i]] ps
      [mkC (.waved .plus) (liftA 2 (.inr x)) (newA 0), mkC (.waved .s) (newA 0) (newA 1),
        mkC (.G .plus) (newA 1) (newA 0)]
      (by rw [hsΔ]; exact hperm.trans (List.Perm.append_right _ hpf)) ?_
      (Local_pathOK_dPieces _ hps rfl rfl (Local_atX hb2).2 (Local_atX ha2).2) hR ?_
      (Local_m3_2 (w := .plus) (w' := .s) (by simp) (by simp)) ?_
    · have hs' : (f.eraseIdx i').map Local_stripC = f.eraseIdx i' :=
        Local_strip_labelFree (Γ := ⟨_, 0⟩) fun c hc => hflf c (List.mem_of_mem_eraseIdx hc)
      simp [List.map_append, Local_strip_liftCs, hs', Local_strip_dPieces hps, Local_strip_mkC]
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact Local_newOK_mkC _ (kW _) hx2 ha2
      · exact Local_newOK_mkC _ (kW _) ha2 hb2
      · exact Local_newOK_mkC _ (kG _) hb2 ha2
    · intro c hc pq u hlu
      exfalso
      simp only [List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · rw [Local_label_liftCs (fun c hc => hflf c (List.mem_of_mem_eraseIdx hc)) c hc] at hlu
        simp at hlu
      · rw [Local_label_dPieces hps c hc] at hlu; simp at hlu
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl <;> simp [mkC] at hlu
  · -- `Q_x` of the graph
    refine Local_decT_mk0 _ _ (by rw [Local_strip_labelQs]) ?_
    intro c hc pq u hlu
    exact Local_label_labelQs (fun c hc => hlf c hc) c hc pq u hlu
  · -- `Q_α`
    refine Local_decT_mk 1 _ _ f [] [Δ.comps[i]] [] [mkC (.light .plus) (newA 0) (newA 0),
      mkC (.waved .plus) (liftA 1 (.inr x)) (newA 0)] (by rw [hsΔ]; simpa using hperm) ?_
      (Or.inl ⟨rfl, rfl⟩) hR ?_ (Local_m3_1 (w := .plus) (by simp)) ?_
    · simp [List.map_append, Local_strip_labelQs, Local_strip_liftCs, hsf, Local_strip_mkC]
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact Local_newOK_mkC _ (kL _) ha1 ha1
      · exact Local_newOK_mkC _ (kW _) hx1 ha1
    · intro c hc pq u hlu
      rcases List.mem_append.1 hc with hc | hc
      · rw [Local_label_labelQs (by
          intro c hc
          rcases List.mem_append.1 hc with hc | hc
          · exact Local_label_liftCs hflf c hc
          · simp only [List.mem_singleton] at hc; rw [hc]; rfl) c hc pq u hlu]
        exact ha1
      · simp only [List.mem_singleton] at hc
        rw [hc] at hlu; simp [mkC] at hlu
  · -- `Q_x` of the weight term
    refine Local_decT_mk 1 _ _ f [] [Δ.comps[i]] [] [mkC (.light .plus) (newA 0) (newA 0),
      mkC (.weight .plus) (liftA 1 (.inr x)) (liftA 1 (.inr x)),
      mkC (.waved .s) (liftA 1 (.inr x)) (newA 0)] (by rw [hsΔ]; simpa using hperm) ?_
      (Or.inl ⟨rfl, rfl⟩) hR ?_ (Local_m3_1 (w := .s) (by simp)) ?_
    · simp [List.map_append, Local_strip_labelQs, Local_strip_liftCs, hsf, Local_strip_mkC]
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact Local_newOK_mkC _ (kL _) ha1 ha1
      · exact Local_newOK_mkC _ (kWt _) hx1 hx1
      · exact Local_newOK_mkC _ (kW _) hx1 ha1
    · intro c hc pq u hlu
      rcases List.mem_append.1 hc with hc | hc
      · rw [Local_label_labelQs (by
          intro c hc
          rcases List.mem_append.1 hc with hc | hc
          · exact Local_label_liftCs hflf c hc
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl <;> rfl) c hc pq u hlu]
        exact hx1
      · simp only [List.mem_singleton] at hc
        rw [hc] at hlu; simp [mkC] at hlu
  · -- `Q_α` of the two new atoms
    refine Local_decT_mk 2 _ _ f [] [Δ.comps[i]] [] [mkC (.light .plus) (newA 1) (newA 1),
      mkC (.weight .plus) (newA 0) (newA 0), mkC (.waved .plus) (liftA 2 (.inr x)) (newA 0),
      mkC (.waved .s) (newA 0) (newA 1)] (by rw [hsΔ]; simpa using hperm) ?_
      (Or.inl ⟨rfl, rfl⟩) hR ?_ (Local_m3_2 (w := .plus) (w' := .s) (by simp) (by simp)) ?_
    · simp [List.map_append, Local_strip_labelQs, Local_strip_liftCs, hsf, Local_strip_mkC]
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact Local_newOK_mkC _ (kL _) hb2 hb2
      · exact Local_newOK_mkC _ (kWt _) ha2 ha2
      · exact Local_newOK_mkC _ (kW _) hx2 ha2
      · exact Local_newOK_mkC _ (kW _) ha2 hb2
    · intro c hc pq u hlu
      rcases List.mem_append.1 hc with hc | hc
      · rw [Local_label_labelQs (by
          intro c hc
          rcases List.mem_append.1 hc with hc | hc
          · exact Local_label_liftCs hflf c hc
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl <;> rfl) c hc pq u hlu]
        exact ha2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp [mkC] at hlu
  · -- `Q_x` of the derivative terms with one new atom
    obtain ⟨i', hi', ps, hps, rfl, hpf⟩ := Local_dTerms_lift hd
    refine Local_decT_mk 1 _ _ (f.eraseIdx i') [f[i']] [Δ.comps[i]] ps
      [mkC (.G .plus) (newA 0) (liftA 1 (.inr x)), mkC (.waved .s) (liftA 1 (.inr x)) (newA 0)]
      (by rw [hsΔ]; exact hperm.trans (List.Perm.append_right _ hpf)) ?_
      (Local_pathOK_dPieces _ hps rfl rfl (Local_atX ha1).2 (Local_atX hx1).2) hR ?_
      (Local_m3_1 (w := .s) (by simp)) ?_
    · have hs' : (f.eraseIdx i').map Local_stripC = f.eraseIdx i' :=
        Local_strip_labelFree (Γ := ⟨_, 0⟩) fun c hc => hflf c (List.mem_of_mem_eraseIdx hc)
      simp [List.map_append, Local_strip_labelQs, Local_strip_liftCs, hs', Local_strip_dPieces hps,
        Local_strip_mkC]
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact Local_newOK_mkC _ (kG _) ha1 hx1
      · exact Local_newOK_mkC _ (kW _) hx1 ha1
    · intro c hc pq u hlu
      rcases List.mem_append.1 hc with hc | hc
      · rw [Local_label_labelQs (by
          intro c hc
          simp only [List.mem_append] at hc
          rcases hc with (hc | hc) | hc
          · exact Local_label_liftCs (fun c hc => hflf c (List.mem_of_mem_eraseIdx hc)) c hc
          · exact Local_label_dPieces hps c hc
          · simp only [List.mem_singleton] at hc; rw [hc]; rfl) c hc pq u hlu]
        exact hx1
      · simp only [List.mem_singleton] at hc
        rw [hc] at hlu; simp [mkC] at hlu
  · -- `Q_α` of the derivative terms with two new atoms
    obtain ⟨i', hi', ps, hps, rfl, hpf⟩ := Local_dTerms_lift hd
    refine Local_decT_mk 2 _ _ (f.eraseIdx i') [f[i']] [Δ.comps[i]] ps
      [mkC (.G .plus) (newA 1) (newA 0), mkC (.waved .plus) (liftA 2 (.inr x)) (newA 0),
        mkC (.waved .s) (newA 0) (newA 1)]
      (by rw [hsΔ]; exact hperm.trans (List.Perm.append_right _ hpf)) ?_
      (Local_pathOK_dPieces _ hps rfl rfl (Local_atX hb2).2 (Local_atX ha2).2) hR ?_
      (Local_m3_2 (w := .plus) (w' := .s) (by simp) (by simp)) ?_
    · have hs' : (f.eraseIdx i').map Local_stripC = f.eraseIdx i' :=
        Local_strip_labelFree (Γ := ⟨_, 0⟩) fun c hc => hflf c (List.mem_of_mem_eraseIdx hc)
      simp [List.map_append, Local_strip_labelQs, Local_strip_liftCs, hs', Local_strip_dPieces hps,
        Local_strip_mkC]
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact Local_newOK_mkC _ (kG _) hb2 ha2
      · exact Local_newOK_mkC _ (kW _) hx2 ha2
      · exact Local_newOK_mkC _ (kW _) ha2 hb2
    · intro c hc pq u hlu
      rcases List.mem_append.1 hc with hc | hc
      · rw [Local_label_labelQs (by
          intro c hc
          simp only [List.mem_append] at hc
          rcases hc with (hc | hc) | hc
          · exact Local_label_liftCs (fun c hc => hflf c (List.mem_of_mem_eraseIdx hc)) c hc
          · exact Local_label_dPieces hps c hc
          · simp only [List.mem_singleton] at hc; rw [hc]; rfl) c hc pq u hlu]
        exact ha2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp [mkC] at hlu

/-- The construction of `Local_DecT` for a term `⟨cs, d⟩` with `j` new atoms and replaced
components. -/
private theorem Local_decT_mkD {Δ : Graph 3 n} {x : Fin n} (j : ℕ)
    (cs : List (Comp (Atom 3 (n + j)))) (d : Coeff)
    (K D P R : List (Comp (Atom 3 n))) (D' P' N : List (Comp (Atom 3 (n + j))))
    (h1 : (Δ.comps.map Local_stripC).Perm (K ++ D ++ P ++ R))
    (h2 : (liftCs j K ++ D' ++ P' ++ N).Perm (cs.map Local_stripC))
    (h3 : List.Forall₂ (Local_MovR Δ x j) D D')
    (h4 : Local_PathOK Δ x j P P') (h5 : ∀ c ∈ R, c.kind.isWeight = true)
    (h6 : ∀ c ∈ N, Local_NewOK Δ x j c)
    (h7 : ∀ i : Fin j, (⟨cs, d⟩ : Graph 3 (n + j)).molGraph.Reachable (newA i) (liftA j (.inr x)))
    (hl : ∀ c ∈ cs, ∀ pq u, c.label = some (pq, u) → Local_AtX x u) :
    Local_DecT Δ x ⟨n + j, ⟨cs, d⟩, liftA j⟩ :=
  ⟨j, rfl, fun _ => rfl, ⟨K, D, P, R, D', P', N, h1, h2, h3, h4, h5, h6, h7⟩,
    fun c hc pq u hlu => (Local_atX (Γ := Δ) (hl c hc pq u hlu)).2⟩

/-- A component of the graph replaced by one of the same kind, ends read the same way. -/
private theorem Local_movR_mk {Δ : Graph 3 n} {x : Fin n} {j : ℕ} (d : Comp (Atom 3 n))
    (d' : Comp (Atom 3 (n + j))) (hk : d'.kind = d.kind) (hr : d.kind.isRandom = true)
    (hx : d'.x = liftA j d.x ∨ (d.x.isRight = true ∧ d'.x.isRight = true))
    (hy : d'.y = liftA j d.y ∨ (d.y.isRight = true ∧ d'.y.isRight = true))
    (hπx : Local_proj j x d'.x = d.x) (hπy : Local_proj j x d'.y = d.y) :
    Local_MovR Δ x j d d' := by
  refine ⟨Or.inl hk, hr, hx, hy, ?_⟩
  unfold Local_SameR
  have e : Local_rd Δ (d'.map (Local_proj j x)) = Local_rd Δ d := by
    simp only [Local_rd, Comp.map, hk, hπx, hπy]
  rw [e]
  exact Local_Same.refl _

private theorem Local_mem_edgeIdx {Γ : Graph 3 n} {u : Atom 3 n} {ch : Charge} {out : Bool} {i : ℕ}
    (h : i ∈ Γ.edgeIdx u ch out) : ∃ hi : i < Γ.comps.length, Γ.comps[i].kind = .G ch ∧
      (out = true → Γ.comps[i].x = u ∧ Γ.comps[i].y ≠ u) ∧
      (out = false → Γ.comps[i].y = u ∧ Γ.comps[i].x ≠ u) := by
  unfold Graph.edgeIdx at h
  obtain ⟨⟨c, i'⟩, hp, rfl⟩ := List.mem_map.1 h
  obtain ⟨hz, hpred⟩ := List.mem_filter.1 hp
  obtain ⟨-, hlt, hc⟩ := List.mem_zipIdx hz
  simp only [Nat.zero_add, Nat.sub_zero] at hlt hc
  refine ⟨hlt, ?_⟩
  simp only at hpred ⊢
  rw [← hc]
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  obtain ⟨hk, hd⟩ := hpred
  refine ⟨hk, fun ho => ?_, fun ho => ?_⟩
  · subst ho
    simp only [if_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hd
    exact hd
  · subst ho
    simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
      ne_eq] at hd
    exact hd

/-- Lists equal up to order, by counting. -/
local macro "perm_tac" : tactic =>
  `(tactic| (classical
             rw [List.perm_iff_count]
             intro z
             simp only [List.count_append, List.count_cons, List.count_nil]
             omega))

/-- **The multi-edge expansion, case (i)**: the terms of [I, (3.13)] at an internal atom `x` of a
graph without labels have the form of `Local_Dec`. -/
private theorem Local_mEO_decT {Δ : Graph 3 n} (hlf : Δ.LabelFree) (x : Fin n)
    {E : TExpansion 3 n} (hE : multiEOut (.inr x) Δ = some E) : ∀ t ∈ E, Local_DecT Δ x t := by
  unfold multiEOut at hE
  split at hE
  · simp at hE
  rename_i i₁ is₂ hI
  split at hE
  · simp at hE
  rename_i e₁ he₁
  dsimp only at hE
  split at hE
  · simp at hE
  rename_i hxd
  obtain rfl := Option.some.inj hE
  have hi₁m : i₁ ∈ Δ.edgeIdx (.inr x) .plus true := by rw [hI]; exact List.mem_cons_self
  obtain ⟨hi₁, hk₁, hx₁, -⟩ := Local_mem_edgeIdx hi₁m
  obtain ⟨hx₁, hy₁⟩ := hx₁ rfl
  have he₁ : e₁ = Δ.comps[i₁] := by
    rw [List.getElem?_eq_getElem hi₁] at he₁
    exact (Option.some.inj he₁).symm
  subst he₁
  have hsΔ : Δ.comps.map Local_stripC = Δ.comps := Local_strip_labelFree hlf
  have hsub : ∀ l : List (Comp (Atom 3 n)), (∀ c ∈ l, c ∈ Δ.comps) → l.map Local_stripC = l :=
    fun l h => Local_strip_labelFree (Γ := ⟨l, 0⟩) fun c hc => hlf c (h c hc)
  have hlfl : ∀ l : List (Comp (Atom 3 n)), (∀ c ∈ l, c ∈ Δ.comps) → ∀ c ∈ l, c.label = none :=
    fun l h c hc => hlf c (h c hc)
  have hx1 : Local_AtX x (liftA 1 (.inr x) : Atom 3 (n + 1)) := Or.inl rfl
  have ha1 : Local_AtX x (newA 0 : Atom 3 (n + 1)) := Or.inr ⟨0, rfl⟩
  have kW : ∀ w, ((∃ w', Kind.waved w = .waved w') ∨ (∃ ch, Kind.waved w = .light ch) ∨
      (∃ ch, Kind.waved w = .weight ch) ∨ (∃ ch, Kind.waved w = .G ch)) := fun w => Or.inl ⟨w, rfl⟩
  have kL : ∀ c, ((∃ w', Kind.light c = .waved w') ∨ (∃ ch, Kind.light c = .light ch) ∨
      (∃ ch, Kind.light c = .weight ch) ∨ (∃ ch, Kind.light c = .G ch)) :=
    fun c => Or.inr (Or.inl ⟨c, rfl⟩)
  have kWt : ∀ c, ((∃ w', Kind.weight c = .waved w') ∨ (∃ ch, Kind.weight c = .light ch) ∨
      (∃ ch, Kind.weight c = .weight ch) ∨ (∃ ch, Kind.weight c = .G ch)) :=
    fun c => Or.inr (Or.inr (Or.inl ⟨c, rfl⟩))
  have kG : ∀ c, ((∃ w', Kind.G c = .waved w') ∨ (∃ ch, Kind.G c = .light ch) ∨
      (∃ ch, Kind.G c = .weight ch) ∨ (∃ ch, Kind.G c = .G ch)) :=
    fun c => Or.inr (Or.inr (Or.inr ⟨c, rfl⟩))
  -- the edge `G_{x y₁}` moved to `α`
  have hM₁ : Local_MovR Δ x 1 Δ.comps[i₁]
      (mkC (.G .plus) (newA 0) (liftA 1 Δ.comps[i₁].y)) :=
    Local_movR_mk _ _ (by simp [mkC, hk₁]) (by rw [hk₁]; rfl)
      (Or.inr ⟨by rw [hx₁]; rfl, rfl⟩) (Or.inl rfl)
      (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hx₁]) (Local_proj_lift _ _ _)
  -- the other solid edges at `x`
  have famM : ∀ j ∈ Δ.edgeIdx (.inr x) .minus true, ∃ hj : j < Δ.comps.length,
      Δ.comps[j].kind = .G .minus ∧ Δ.comps[j].x = .inr x ∧ j ≠ i₁ := by
    intro j hj
    obtain ⟨hjl, hk, hxy, -⟩ := Local_mem_edgeIdx hj
    refine ⟨hjl, hk, (hxy rfl).1, fun h => ?_⟩
    subst h
    rw [hk₁] at hk
    simp at hk
  have famP : ∀ j ∈ Δ.edgeIdx (.inr x) .plus false, ∃ hj : j < Δ.comps.length,
      Δ.comps[j].kind = .G .plus ∧ Δ.comps[j].y = .inr x ∧ j ≠ i₁ := by
    intro j hj
    obtain ⟨hjl, hk, -, hxy⟩ := Local_mem_edgeIdx hj
    refine ⟨hjl, hk, (hxy rfl).1, fun h => ?_⟩
    subst h
    exact hy₁ (hxy rfl).1
  have hsE : ∀ S : List ℕ, (eraseIdxs S Δ.comps).map Local_stripC = eraseIdxs S Δ.comps :=
    fun S => hsub _ fun c hc => Local_mem_eraseIdxs hc
  have hsR : (Δ.comps.eraseIdx i₁).map Local_stripC = Δ.comps.eraseIdx i₁ :=
    hsub _ fun c hc => List.mem_of_mem_eraseIdx hc
  have hsP : ∀ S : List ℕ, (pickIdxs S Δ.comps).map Local_stripC = pickIdxs S Δ.comps :=
    fun S => hsub _ fun c hc => Local_mem_pickIdxs hc
  have hlE : ∀ S : List ℕ, ∀ c ∈ liftCs 1 (eraseIdxs S Δ.comps), c.label = none :=
    fun S => Local_label_liftCs (hlfl _ fun c hc => Local_mem_eraseIdxs hc)
  have hlR : ∀ c ∈ liftCs 1 (Δ.comps.eraseIdx i₁), c.label = none :=
    Local_label_liftCs (hlfl _ fun c hc => List.mem_of_mem_eraseIdx hc)
  have hlP : ∀ S : List ℕ, ∀ c ∈ liftCs 1 (pickIdxs S Δ.comps), c.label = none :=
    fun S => Local_label_liftCs (hlfl _ fun c hc => Local_mem_pickIdxs hc)
  have hlΔ : ∀ c ∈ liftCs 1 Δ.comps, c.label = none := Local_label_liftCs hlf
  have hsx : Local_NewOK Δ x 1 (mkC (.waved .s) (liftA 1 (.inr x)) (newA 0)) :=
    Local_newOK_mkC _ (kW _) hx1 ha1
  intro t ht
  simp only [List.mem_append, List.mem_ite_nil_left, List.mem_map, List.mem_singleton] at ht
  rcases ht with ((((((((((((((⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | rfl) |
    ⟨-, rfl⟩) | ⟨-, rfl⟩) | ⟨d', ⟨d, hd, rfl⟩, rfl⟩) | rfl) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | rfl) |
    ⟨-, rfl⟩) | ⟨-, rfl⟩) | ⟨d', ⟨d, hd, rfl⟩, rfl⟩)
  · obtain ⟨hjl, hkj, hxj, hji⟩ := famM j hj
    have hgd : (Δ.comps.getD j Δ.comps[i₁]) = Δ.comps[j] := List.getD_eq_getElem _ _ hjl
    simp only [hgd]
    refine Local_decT_mkD 1 _ _ (eraseIdxs [i₁, j] Δ.comps) [Δ.comps[i₁], Δ.comps[j]] [] []
      [mkC (.G .plus) (newA 0) (liftA 1 Δ.comps[i₁].y), mkC (.G .minus) (newA 0) (liftA 1 Δ.comps[j].y)] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0)] (by rw [hsΔ]; simpa using Local_eraseIdxs2_perm Δ.comps i₁ j hi₁ hjl hji.symm) ?_
      (.cons hM₁ (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
          (Or.inr ⟨by rw [hxj]; rfl, rfl⟩) (Or.inl rfl)
          (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hxj]) (Local_proj_lift _ _ _)) .nil)) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsE, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc
      · subst hc; exact hsx
    · intro c hc pq u hlu
      exfalso
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc | hc | hc
      · rw [hlE _ c hc] at hlu; simp at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
  · obtain ⟨hjl, hkj, hxj, hji⟩ := famP j hj
    have hgd : (Δ.comps.getD j Δ.comps[i₁]) = Δ.comps[j] := List.getD_eq_getElem _ _ hjl
    simp only [hgd]
    refine Local_decT_mkD 1 _ _ (eraseIdxs [i₁, j] Δ.comps) [Δ.comps[i₁], Δ.comps[j]] [] []
      [mkC (.G .plus) (newA 0) (liftA 1 Δ.comps[i₁].y), mkC (.G .plus) (liftA 1 Δ.comps[j].x) (newA 0)] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0)] (by rw [hsΔ]; simpa using Local_eraseIdxs2_perm Δ.comps i₁ j hi₁ hjl hji.symm) ?_
      (.cons hM₁ (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
          (Or.inl rfl) (Or.inr ⟨by rw [hxj]; rfl, rfl⟩)
          (Local_proj_lift _ _ _) (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hxj])) .nil)) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsE, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc
      · subst hc; exact hsx
    · intro c hc pq u hlu
      exfalso
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc | hc | hc
      · rw [hlE _ c hc] at hlu; simp at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
  · obtain ⟨hjl, hkj, hxj, hji⟩ := famM j hj
    have hgd : (Δ.comps.getD j Δ.comps[i₁]) = Δ.comps[j] := List.getD_eq_getElem _ _ hjl
    simp only [hgd]
    refine Local_decT_mkD 1 _ _ (eraseIdxs [i₁, j] Δ.comps) [Δ.comps[i₁], Δ.comps[j]] [] []
      [mkC (.G .plus) (newA 0) (liftA 1 Δ.comps[i₁].y), mkC (.G .minus) (newA 0) (liftA 1 Δ.comps[j].y)] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0), mkC (.light .minus) (liftA 1 (.inr x)) (liftA 1 (.inr x))] (by rw [hsΔ]; simpa using Local_eraseIdxs2_perm Δ.comps i₁ j hi₁ hjl hji.symm) ?_
      (.cons hM₁ (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
          (Or.inr ⟨by rw [hxj]; rfl, rfl⟩) (Or.inl rfl)
          (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hxj]) (Local_proj_lift _ _ _)) .nil)) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsE, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc
      · subst hc; exact hsx
      · subst hc; exact Local_newOK_mkC _ (kL _) hx1 hx1
    · intro c hc pq u hlu
      exfalso
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc | hc | hc | hc
      · rw [hlE _ c hc] at hlu; simp at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
  · obtain ⟨hjl, hkj, hxj, hji⟩ := famP j hj
    have hgd : (Δ.comps.getD j Δ.comps[i₁]) = Δ.comps[j] := List.getD_eq_getElem _ _ hjl
    simp only [hgd]
    refine Local_decT_mkD 1 _ _ (eraseIdxs [i₁, j] Δ.comps) [Δ.comps[i₁], Δ.comps[j]] [] []
      [mkC (.G .plus) (newA 0) (liftA 1 Δ.comps[i₁].y), mkC (.G .plus) (liftA 1 Δ.comps[j].x) (newA 0)] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0), mkC (.light .plus) (liftA 1 (.inr x)) (liftA 1 (.inr x))] (by rw [hsΔ]; simpa using Local_eraseIdxs2_perm Δ.comps i₁ j hi₁ hjl hji.symm) ?_
      (.cons hM₁ (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
          (Or.inl rfl) (Or.inr ⟨by rw [hxj]; rfl, rfl⟩)
          (Local_proj_lift _ _ _) (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hxj])) .nil)) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsE, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc
      · subst hc; exact hsx
      · subst hc; exact Local_newOK_mkC _ (kL _) hx1 hx1
    · intro c hc pq u hlu
      exfalso
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc | hc | hc | hc
      · rw [hlE _ c hc] at hlu; simp at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
  · refine Local_decT_mkD 1 _ _ Δ.comps [] [] [] [] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0), mkC (.light .plus) (newA 0) (newA 0)]
      (by rw [hsΔ]; simp) ?_ .nil (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsΔ, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc
      · subst hc; exact hsx
      · subst hc; exact Local_newOK_mkC _ (kL _) ha1 ha1
    · intro c hc pq u hlu
      exfalso
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc | hc
      · rw [hlΔ c hc] at hlu; simp at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
  · refine Local_decT_mkD 1 _ _ (Δ.comps.eraseIdx i₁) [Δ.comps[i₁]] [] []
      [mkC (.G .plus) (newA 0) (liftA 1 Δ.comps[i₁].y)] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0), mkC (.G .plus) (liftA 1 (.inr x)) (newA 0)]
      (by rw [hsΔ]; simpa using Local_eraseIdx_perm Δ.comps i₁ hi₁) ?_
      (.cons hM₁ .nil) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsR, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc
      · subst hc; exact hsx
      · subst hc; exact Local_newOK_mkC _ (kG _) hx1 ha1
    · intro c hc pq u hlu
      exfalso
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc | hc | hc
      · rw [hlR c hc] at hlu; simp at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
  · refine Local_decT_mkD 1 _ _ (Δ.comps.eraseIdx i₁) [Δ.comps[i₁]] [] []
      [mkC (.G .plus) (newA 0) (liftA 1 Δ.comps[i₁].y)] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0), mkC (.G .minus) (newA 0) (liftA 1 (.inr x))]
      (by rw [hsΔ]; simpa using Local_eraseIdx_perm Δ.comps i₁ hi₁) ?_
      (.cons hM₁ .nil) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsR, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc
      · subst hc; exact hsx
      · subst hc; exact Local_newOK_mkC _ (kG _) ha1 hx1
    · intro c hc pq u hlu
      exfalso
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc | hc | hc
      · rw [hlR c hc] at hlu; simp at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
  · obtain ⟨i', hi', ps, hps, rfl, hpf⟩ := Local_dTerms_lift hd
    have hi₁x : i₁ ∈ (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) := by simp [hi₁m]
    have hs' : ((eraseIdxs (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i').map Local_stripC =
        (eraseIdxs (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i' :=
      hsub _ fun c hc => Local_mem_eraseIdxs (List.mem_of_mem_eraseIdx hc)
    have hlD : ∀ c ∈ liftCs 1 ((eraseIdxs (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i'), c.label = none :=
      Local_label_liftCs (hlfl _ fun c hc => Local_mem_eraseIdxs (List.mem_of_mem_eraseIdx hc))
    have hperm : (Δ.comps.map Local_stripC).Perm
        ((pickIdxs ((Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false).filter (· != i₁)) Δ.comps ++ (eraseIdxs (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i') ++
          [Δ.comps[i₁]] ++ [(eraseIdxs (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps)[i']] ++ []) := by
      rw [hsΔ]
      have p1 := Local_eraseIdxs_pick_perm (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps
      have p2 := Local_pick_split (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps i₁ hi₁ hi₁x
      have p3 := hpf
      classical
      rw [List.perm_iff_count]
      intro z
      have c1 := p1.count_eq z
      have c2 := p2.count_eq z
      have c3 := p3.count_eq z
      simp only [List.count_append, List.count_cons, List.count_nil] at c1 c2 c3 ⊢
      omega
    refine Local_decT_mkD 1 _ _ (pickIdxs ((Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false).filter (· != i₁)) Δ.comps ++
      (eraseIdxs (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i') [Δ.comps[i₁]] [(eraseIdxs (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps)[i']] []
      [mkC (.G .plus) (newA 0) (liftA 1 Δ.comps[i₁].y)] ps
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0)] hperm ?_
      (.cons hM₁ .nil) (Local_pathOK_dPieces _ hps rfl rfl (Local_atX ha1).2 (Local_atX hx1).2)
      (by simp) ?_ (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsP, hs', Local_strip_dPieces hps, List.map_cons, List.map_nil, Local_liftCs_append]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc
      · subst hc; exact hsx
    · intro c hc pq u hlu
      exfalso
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc | hc | hc | hc
      · rw [hlP _ c hc] at hlu; simp at hlu
      · rw [hlD c hc] at hlu; simp at hlu
      · rw [Local_label_dPieces hps c hc] at hlu; simp at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
  · refine Local_decT_mk0 _ _ (by rw [Local_strip_labelQs]) ?_
    intro c hc pq u hlu
    exact Local_label_labelQs (fun c hc => hlf c hc) c hc pq u hlu
  · obtain ⟨hjl, hkj, hxj, hji⟩ := famM j hj
    have hgd : (Δ.comps.getD j Δ.comps[i₁]) = Δ.comps[j] := List.getD_eq_getElem _ _ hjl
    simp only [hgd]
    refine Local_decT_mkD 1 _ _ (eraseIdxs [i₁, j] Δ.comps) [Δ.comps[i₁], Δ.comps[j]] [] []
      [mkC (.G .plus) (newA 0) (liftA 1 Δ.comps[i₁].y), mkC (.G .minus) (newA 0) (liftA 1 Δ.comps[j].y)] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0), mkC (.weight .minus) (liftA 1 (.inr x)) (liftA 1 (.inr x))] (by rw [hsΔ]; simpa using Local_eraseIdxs2_perm Δ.comps i₁ j hi₁ hjl hji.symm) ?_
      (.cons hM₁ (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
          (Or.inr ⟨by rw [hxj]; rfl, rfl⟩) (Or.inl rfl)
          (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hxj]) (Local_proj_lift _ _ _)) .nil)) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsE, Local_strip_labelQs, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc
      · subst hc; exact hsx
      · subst hc; exact Local_newOK_mkC _ (kWt _) hx1 hx1
    · intro c hc pq u hlu
      rw [Local_label_labelQs (fun c hc => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc | hc | hc
          · exact hlE _ c hc
          · subst hc; rfl
          · subst hc; rfl
          · subst hc; rfl
          · subst hc; rfl
          ) c hc pq u hlu]
      exact hx1
  · obtain ⟨hjl, hkj, hxj, hji⟩ := famP j hj
    have hgd : (Δ.comps.getD j Δ.comps[i₁]) = Δ.comps[j] := List.getD_eq_getElem _ _ hjl
    simp only [hgd]
    refine Local_decT_mkD 1 _ _ (eraseIdxs [i₁, j] Δ.comps) [Δ.comps[i₁], Δ.comps[j]] [] []
      [mkC (.G .plus) (newA 0) (liftA 1 Δ.comps[i₁].y), mkC (.G .plus) (liftA 1 Δ.comps[j].x) (newA 0)] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0), mkC (.weight .plus) (liftA 1 (.inr x)) (liftA 1 (.inr x))] (by rw [hsΔ]; simpa using Local_eraseIdxs2_perm Δ.comps i₁ j hi₁ hjl hji.symm) ?_
      (.cons hM₁ (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
          (Or.inl rfl) (Or.inr ⟨by rw [hxj]; rfl, rfl⟩)
          (Local_proj_lift _ _ _) (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hxj])) .nil)) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsE, Local_strip_labelQs, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc
      · subst hc; exact hsx
      · subst hc; exact Local_newOK_mkC _ (kWt _) hx1 hx1
    · intro c hc pq u hlu
      rw [Local_label_labelQs (fun c hc => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc | hc | hc
          · exact hlE _ c hc
          · subst hc; rfl
          · subst hc; rfl
          · subst hc; rfl
          · subst hc; rfl
          ) c hc pq u hlu]
      exact hx1
  · refine Local_decT_mkD 1 _ _ Δ.comps [] [] [] [] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0), mkC (.light .plus) (newA 0) (newA 0)]
      (by rw [hsΔ]; simp) ?_ .nil (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsΔ, Local_strip_labelQs, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc
      · subst hc; exact hsx
      · subst hc; exact Local_newOK_mkC _ (kL _) ha1 ha1
    · intro c hc pq u hlu
      rw [Local_label_labelQs (fun c hc => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc
          · exact hlΔ c hc
          · subst hc; rfl
          · subst hc; rfl
          ) c hc pq u hlu]
      exact hx1
  · refine Local_decT_mkD 1 _ _ (Δ.comps.eraseIdx i₁) [Δ.comps[i₁]] [] []
      [mkC (.G .plus) (newA 0) (liftA 1 Δ.comps[i₁].y)] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0), mkC (.G .plus) (liftA 1 (.inr x)) (newA 0)]
      (by rw [hsΔ]; simpa using Local_eraseIdx_perm Δ.comps i₁ hi₁) ?_
      (.cons hM₁ .nil) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsR, Local_strip_labelQs, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc
      · subst hc; exact hsx
      · subst hc; exact Local_newOK_mkC _ (kG _) hx1 ha1
    · intro c hc pq u hlu
      rw [Local_label_labelQs (fun c hc => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc | hc
          · exact hlR c hc
          · subst hc; rfl
          · subst hc; rfl
          · subst hc; rfl
          ) c hc pq u hlu]
      exact hx1
  · refine Local_decT_mkD 1 _ _ (Δ.comps.eraseIdx i₁) [Δ.comps[i₁]] [] []
      [mkC (.G .plus) (newA 0) (liftA 1 Δ.comps[i₁].y)] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0), mkC (.G .minus) (newA 0) (liftA 1 (.inr x))]
      (by rw [hsΔ]; simpa using Local_eraseIdx_perm Δ.comps i₁ hi₁) ?_
      (.cons hM₁ .nil) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsR, Local_strip_labelQs, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc
      · subst hc; exact hsx
      · subst hc; exact Local_newOK_mkC _ (kG _) ha1 hx1
    · intro c hc pq u hlu
      rw [Local_label_labelQs (fun c hc => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc | hc
          · exact hlR c hc
          · subst hc; rfl
          · subst hc; rfl
          · subst hc; rfl
          ) c hc pq u hlu]
      exact hx1
  · obtain ⟨i', hi', ps, hps, rfl, hpf⟩ := Local_dTerms_lift hd
    have hi₁x : i₁ ∈ (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) := by simp [hi₁m]
    have hs' : ((eraseIdxs (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i').map Local_stripC =
        (eraseIdxs (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i' :=
      hsub _ fun c hc => Local_mem_eraseIdxs (List.mem_of_mem_eraseIdx hc)
    have hlD : ∀ c ∈ liftCs 1 ((eraseIdxs (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i'), c.label = none :=
      Local_label_liftCs (hlfl _ fun c hc => Local_mem_eraseIdxs (List.mem_of_mem_eraseIdx hc))
    have hperm : (Δ.comps.map Local_stripC).Perm
        ((pickIdxs ((Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false).filter (· != i₁)) Δ.comps ++ (eraseIdxs (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i') ++
          [Δ.comps[i₁]] ++ [(eraseIdxs (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps)[i']] ++ []) := by
      rw [hsΔ]
      have p1 := Local_eraseIdxs_pick_perm (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps
      have p2 := Local_pick_split (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps i₁ hi₁ hi₁x
      have p3 := hpf
      classical
      rw [List.perm_iff_count]
      intro z
      have c1 := p1.count_eq z
      have c2 := p2.count_eq z
      have c3 := p3.count_eq z
      simp only [List.count_append, List.count_cons, List.count_nil] at c1 c2 c3 ⊢
      omega
    refine Local_decT_mkD 1 _ _ (pickIdxs ((Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false).filter (· != i₁)) Δ.comps ++
      (eraseIdxs (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i') [Δ.comps[i₁]] [(eraseIdxs (Δ.edgeIdx (.inr x) .plus true ++ Δ.edgeIdx (.inr x) .minus true ++ Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps)[i']] []
      [mkC (.G .plus) (newA 0) (liftA 1 Δ.comps[i₁].y)] ps
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0)] hperm ?_
      (.cons hM₁ .nil) (Local_pathOK_dPieces _ hps rfl rfl (Local_atX ha1).2 (Local_atX hx1).2)
      (by simp) ?_ (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsP, hs', Local_strip_dPieces hps, Local_strip_labelQs, List.map_cons, List.map_nil, Local_liftCs_append]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc
      · subst hc; exact hsx
    · intro c hc pq u hlu
      rw [Local_label_labelQs (fun c hc => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc | hc | hc
          · exact hlP _ c hc
          · exact hlD c hc
          · exact Local_label_dPieces hps c hc
          · subst hc; rfl
          · subst hc; rfl
          ) c hc pq u hlu]
      exact hx1

/-- **The multi-edge expansion, case (iii)**: the terms of [I, (3.14)] at an internal atom `x` of a
graph without labels have the form of `Local_Dec`. -/
private theorem Local_mEI_decT {Δ : Graph 3 n} (hlf : Δ.LabelFree) (x : Fin n)
    {E : TExpansion 3 n} (hE : multiEIn (.inr x) Δ = some E) : ∀ t ∈ E, Local_DecT Δ x t := by
  unfold multiEIn at hE
  split at hE
  · simp at hE
  rename_i i₁ is₂ hI
  split at hE
  · simp at hE
  rename_i e₁ he₁
  dsimp only at hE
  split at hE
  · simp at hE
  rename_i hxd
  obtain rfl := Option.some.inj hE
  have hi₁m : i₁ ∈ Δ.edgeIdx (.inr x) .plus false := by rw [hI]; exact List.mem_cons_self
  obtain ⟨hi₁, hk₁, -, hy₁⟩ := Local_mem_edgeIdx hi₁m
  obtain ⟨hy₁, hx₁⟩ := hy₁ rfl
  have he₁ : e₁ = Δ.comps[i₁] := by
    rw [List.getElem?_eq_getElem hi₁] at he₁
    exact (Option.some.inj he₁).symm
  subst he₁
  have hsΔ : Δ.comps.map Local_stripC = Δ.comps := Local_strip_labelFree hlf
  have hsub : ∀ l : List (Comp (Atom 3 n)), (∀ c ∈ l, c ∈ Δ.comps) → l.map Local_stripC = l :=
    fun l h => Local_strip_labelFree (Γ := ⟨l, 0⟩) fun c hc => hlf c (h c hc)
  have hlfl : ∀ l : List (Comp (Atom 3 n)), (∀ c ∈ l, c ∈ Δ.comps) → ∀ c ∈ l, c.label = none :=
    fun l h c hc => hlf c (h c hc)
  have hx1 : Local_AtX x (liftA 1 (.inr x) : Atom 3 (n + 1)) := Or.inl rfl
  have ha1 : Local_AtX x (newA 0 : Atom 3 (n + 1)) := Or.inr ⟨0, rfl⟩
  have kL : ∀ c, ((∃ w', Kind.light c = .waved w') ∨ (∃ ch, Kind.light c = .light ch) ∨
      (∃ ch, Kind.light c = .weight ch) ∨ (∃ ch, Kind.light c = .G ch)) :=
    fun c => Or.inr (Or.inl ⟨c, rfl⟩)
  have kWt : ∀ c, ((∃ w', Kind.weight c = .waved w') ∨ (∃ ch, Kind.weight c = .light ch) ∨
      (∃ ch, Kind.weight c = .weight ch) ∨ (∃ ch, Kind.weight c = .G ch)) :=
    fun c => Or.inr (Or.inr (Or.inl ⟨c, rfl⟩))
  have kG : ∀ c, ((∃ w', Kind.G c = .waved w') ∨ (∃ ch, Kind.G c = .light ch) ∨
      (∃ ch, Kind.G c = .weight ch) ∨ (∃ ch, Kind.G c = .G ch)) :=
    fun c => Or.inr (Or.inr (Or.inr ⟨c, rfl⟩))
  -- the edge `G_{w₁ x}` moved to `α`
  have hM₁ : Local_MovR Δ x 1 Δ.comps[i₁]
      (mkC (.G .plus) (liftA 1 Δ.comps[i₁].x) (newA 0)) :=
    Local_movR_mk _ _ (by simp [mkC, hk₁]) (by rw [hk₁]; rfl)
      (Or.inl rfl) (Or.inr ⟨by rw [hy₁]; rfl, rfl⟩)
      (Local_proj_lift _ _ _) (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hy₁])
  have famM : ∀ j ∈ Δ.edgeIdx (.inr x) .minus false, ∃ hj : j < Δ.comps.length,
      Δ.comps[j].kind = .G .minus ∧ Δ.comps[j].y = .inr x ∧ j ≠ i₁ := by
    intro j hj
    obtain ⟨hjl, hk, -, hxy⟩ := Local_mem_edgeIdx hj
    refine ⟨hjl, hk, (hxy rfl).1, fun h => ?_⟩
    subst h
    rw [hk₁] at hk
    simp at hk
  have hsE : ∀ S : List ℕ, (eraseIdxs S Δ.comps).map Local_stripC = eraseIdxs S Δ.comps :=
    fun S => hsub _ fun c hc => Local_mem_eraseIdxs hc
  have hsR : (Δ.comps.eraseIdx i₁).map Local_stripC = Δ.comps.eraseIdx i₁ :=
    hsub _ fun c hc => List.mem_of_mem_eraseIdx hc
  have hsP : ∀ S : List ℕ, (pickIdxs S Δ.comps).map Local_stripC = pickIdxs S Δ.comps :=
    fun S => hsub _ fun c hc => Local_mem_pickIdxs hc
  have hlE : ∀ S : List ℕ, ∀ c ∈ liftCs 1 (eraseIdxs S Δ.comps), c.label = none :=
    fun S => Local_label_liftCs (hlfl _ fun c hc => Local_mem_eraseIdxs hc)
  have hlR : ∀ c ∈ liftCs 1 (Δ.comps.eraseIdx i₁), c.label = none :=
    Local_label_liftCs (hlfl _ fun c hc => List.mem_of_mem_eraseIdx hc)
  have hlP : ∀ S : List ℕ, ∀ c ∈ liftCs 1 (pickIdxs S Δ.comps), c.label = none :=
    fun S => Local_label_liftCs (hlfl _ fun c hc => Local_mem_pickIdxs hc)
  have hlΔ : ∀ c ∈ liftCs 1 Δ.comps, c.label = none := Local_label_liftCs hlf
  have hsx : Local_NewOK Δ x 1 (mkC (.waved .s) (liftA 1 (.inr x)) (newA 0)) :=
    Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) hx1 ha1
  intro t ht
  simp only [List.mem_append, List.mem_ite_nil_left, List.mem_map, List.mem_singleton] at ht
  rcases ht with (((((((((⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | rfl) | ⟨-, rfl⟩) | ⟨d', ⟨d, hd, rfl⟩, rfl⟩) |
    rfl) | ⟨j, hj, rfl⟩) | rfl) | ⟨-, rfl⟩) | ⟨d', ⟨d, hd, rfl⟩, rfl⟩)
  · obtain ⟨hjl, hkj, hyj, hji⟩ := famM j hj
    have hgd : (Δ.comps.getD j Δ.comps[i₁]) = Δ.comps[j] := List.getD_eq_getElem _ _ hjl
    simp only [hgd]
    refine Local_decT_mkD 1 _ _ (eraseIdxs [i₁, j] Δ.comps) [Δ.comps[i₁], Δ.comps[j]] [] []
      [mkC (.G .plus) (liftA 1 Δ.comps[i₁].x) (newA 0), mkC (.G .minus) (liftA 1 Δ.comps[j].x) (newA 0)] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0)] (by rw [hsΔ]; simpa using Local_eraseIdxs2_perm Δ.comps i₁ j hi₁ hjl hji.symm) ?_
      (.cons hM₁ (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
          (Or.inl rfl) (Or.inr ⟨by rw [hyj]; rfl, rfl⟩)
          (Local_proj_lift _ _ _) (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hyj])) .nil)) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsE, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc
      · subst hc; exact hsx
    · intro c hc pq u hlu
      exfalso
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc | hc | hc
      · rw [hlE _ c hc] at hlu; simp at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
  · obtain ⟨hjl, hkj, hyj, hji⟩ := famM j hj
    have hgd : (Δ.comps.getD j Δ.comps[i₁]) = Δ.comps[j] := List.getD_eq_getElem _ _ hjl
    simp only [hgd]
    refine Local_decT_mkD 1 _ _ (eraseIdxs [i₁, j] Δ.comps) [Δ.comps[i₁], Δ.comps[j]] [] []
      [mkC (.G .plus) (liftA 1 Δ.comps[i₁].x) (newA 0), mkC (.G .minus) (liftA 1 Δ.comps[j].x) (newA 0)] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0), mkC (.light .minus) (liftA 1 (.inr x)) (liftA 1 (.inr x))] (by rw [hsΔ]; simpa using Local_eraseIdxs2_perm Δ.comps i₁ j hi₁ hjl hji.symm) ?_
      (.cons hM₁ (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
          (Or.inl rfl) (Or.inr ⟨by rw [hyj]; rfl, rfl⟩)
          (Local_proj_lift _ _ _) (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hyj])) .nil)) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsE, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc
      · subst hc; exact hsx
      · subst hc; exact Local_newOK_mkC _ (kL _) hx1 hx1
    · intro c hc pq u hlu
      exfalso
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc | hc | hc | hc
      · rw [hlE _ c hc] at hlu; simp at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
  · refine Local_decT_mkD 1 _ _ Δ.comps [] [] [] [] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0), mkC (.light .plus) (newA 0) (newA 0)]
      (by rw [hsΔ]; simp) ?_ .nil (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsΔ, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc
      · subst hc; exact hsx
      · subst hc; exact Local_newOK_mkC _ (kL _) ha1 ha1
    · intro c hc pq u hlu
      exfalso
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc | hc
      · rw [hlΔ c hc] at hlu; simp at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
  · refine Local_decT_mkD 1 _ _ (Δ.comps.eraseIdx i₁) [Δ.comps[i₁]] [] []
      [mkC (.G .plus) (liftA 1 Δ.comps[i₁].x) (newA 0)] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 (.inr x))]
      (by rw [hsΔ]; simpa using Local_eraseIdx_perm Δ.comps i₁ hi₁) ?_
      (.cons hM₁ .nil) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsR, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc
      · subst hc; exact hsx
      · subst hc; exact Local_newOK_mkC _ (kG _) ha1 hx1
    · intro c hc pq u hlu
      exfalso
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc | hc | hc
      · rw [hlR c hc] at hlu; simp at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
  · obtain ⟨i', hi', ps, hps, rfl, hpf⟩ := Local_dTerms_lift hd
    have hi₁x : i₁ ∈ (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) := by simp [hi₁m]
    have hs' : ((eraseIdxs (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i').map Local_stripC =
        (eraseIdxs (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i' :=
      hsub _ fun c hc => Local_mem_eraseIdxs (List.mem_of_mem_eraseIdx hc)
    have hlD : ∀ c ∈ liftCs 1 ((eraseIdxs (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i'), c.label = none :=
      Local_label_liftCs (hlfl _ fun c hc => Local_mem_eraseIdxs (List.mem_of_mem_eraseIdx hc))
    have hperm : (Δ.comps.map Local_stripC).Perm
        ((pickIdxs ((Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false).filter (· != i₁)) Δ.comps ++ (eraseIdxs (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i') ++
          [Δ.comps[i₁]] ++ [(eraseIdxs (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps)[i']] ++ []) := by
      rw [hsΔ]
      have p1 := Local_eraseIdxs_pick_perm (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps
      have p2 := Local_pick_split (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps i₁ hi₁ hi₁x
      have p3 := hpf
      classical
      rw [List.perm_iff_count]
      intro z
      have c1 := p1.count_eq z
      have c2 := p2.count_eq z
      have c3 := p3.count_eq z
      simp only [List.count_append, List.count_cons, List.count_nil] at c1 c2 c3 ⊢
      omega
    refine Local_decT_mkD 1 _ _ (pickIdxs ((Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false).filter (· != i₁)) Δ.comps ++
      (eraseIdxs (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i') [Δ.comps[i₁]] [(eraseIdxs (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps)[i']] []
      [mkC (.G .plus) (liftA 1 Δ.comps[i₁].x) (newA 0)] ps
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0)] hperm ?_
      (.cons hM₁ .nil) (Local_pathOK_dPieces _ hps rfl rfl (Local_atX hx1).2 (Local_atX ha1).2)
      (by simp) ?_ (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsP, hs', Local_strip_dPieces hps, List.map_cons, List.map_nil, Local_liftCs_append]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc
      · subst hc; exact hsx
    · intro c hc pq u hlu
      exfalso
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc | hc | hc | hc
      · rw [hlP _ c hc] at hlu; simp at hlu
      · rw [hlD c hc] at hlu; simp at hlu
      · rw [Local_label_dPieces hps c hc] at hlu; simp at hlu
      · subst hc; simp [mkC] at hlu
      · subst hc; simp [mkC] at hlu
  · refine Local_decT_mk0 _ _ (by rw [Local_strip_labelQs]) ?_
    intro c hc pq u hlu
    exact Local_label_labelQs (fun c hc => hlf c hc) c hc pq u hlu
  · obtain ⟨hjl, hkj, hyj, hji⟩ := famM j hj
    have hgd : (Δ.comps.getD j Δ.comps[i₁]) = Δ.comps[j] := List.getD_eq_getElem _ _ hjl
    simp only [hgd]
    refine Local_decT_mkD 1 _ _ (eraseIdxs [i₁, j] Δ.comps) [Δ.comps[i₁], Δ.comps[j]] [] []
      [mkC (.G .plus) (liftA 1 Δ.comps[i₁].x) (newA 0), mkC (.G .minus) (liftA 1 Δ.comps[j].x) (newA 0)] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0), mkC (.weight .minus) (liftA 1 (.inr x)) (liftA 1 (.inr x))] (by rw [hsΔ]; simpa using Local_eraseIdxs2_perm Δ.comps i₁ j hi₁ hjl hji.symm) ?_
      (.cons hM₁ (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
          (Or.inl rfl) (Or.inr ⟨by rw [hyj]; rfl, rfl⟩)
          (Local_proj_lift _ _ _) (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hyj])) .nil)) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsE, Local_strip_labelQs, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc
      · subst hc; exact hsx
      · subst hc; exact Local_newOK_mkC _ (kWt _) hx1 hx1
    · intro c hc pq u hlu
      rw [Local_label_labelQs (fun c hc => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc | hc | hc
          · exact hlE _ c hc
          · subst hc; rfl
          · subst hc; rfl
          · subst hc; rfl
          · subst hc; rfl
          ) c hc pq u hlu]
      exact hx1
  · refine Local_decT_mkD 1 _ _ Δ.comps [] [] [] [] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0), mkC (.light .plus) (newA 0) (newA 0)]
      (by rw [hsΔ]; simp) ?_ .nil (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsΔ, Local_strip_labelQs, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc
      · subst hc; exact hsx
      · subst hc; exact Local_newOK_mkC _ (kL _) ha1 ha1
    · intro c hc pq u hlu
      rw [Local_label_labelQs (fun c hc => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc
          · exact hlΔ c hc
          · subst hc; rfl
          · subst hc; rfl
          ) c hc pq u hlu]
      exact hx1
  · refine Local_decT_mkD 1 _ _ (Δ.comps.eraseIdx i₁) [Δ.comps[i₁]] [] []
      [mkC (.G .plus) (liftA 1 Δ.comps[i₁].x) (newA 0)] []
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0), mkC (.G .plus) (newA 0) (liftA 1 (.inr x))]
      (by rw [hsΔ]; simpa using Local_eraseIdx_perm Δ.comps i₁ hi₁) ?_
      (.cons hM₁ .nil) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
      (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsR, Local_strip_labelQs, List.map_cons, List.map_nil]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc | hc
      · subst hc; exact hsx
      · subst hc; exact Local_newOK_mkC _ (kG _) ha1 hx1
    · intro c hc pq u hlu
      rw [Local_label_labelQs (fun c hc => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc | hc
          · exact hlR c hc
          · subst hc; rfl
          · subst hc; rfl
          · subst hc; rfl
          ) c hc pq u hlu]
      exact hx1
  · obtain ⟨i', hi', ps, hps, rfl, hpf⟩ := Local_dTerms_lift hd
    have hi₁x : i₁ ∈ (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) := by simp [hi₁m]
    have hs' : ((eraseIdxs (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i').map Local_stripC =
        (eraseIdxs (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i' :=
      hsub _ fun c hc => Local_mem_eraseIdxs (List.mem_of_mem_eraseIdx hc)
    have hlD : ∀ c ∈ liftCs 1 ((eraseIdxs (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i'), c.label = none :=
      Local_label_liftCs (hlfl _ fun c hc => Local_mem_eraseIdxs (List.mem_of_mem_eraseIdx hc))
    have hperm : (Δ.comps.map Local_stripC).Perm
        ((pickIdxs ((Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false).filter (· != i₁)) Δ.comps ++ (eraseIdxs (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i') ++
          [Δ.comps[i₁]] ++ [(eraseIdxs (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps)[i']] ++ []) := by
      rw [hsΔ]
      have p1 := Local_eraseIdxs_pick_perm (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps
      have p2 := Local_pick_split (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps i₁ hi₁ hi₁x
      have p3 := hpf
      classical
      rw [List.perm_iff_count]
      intro z
      have c1 := p1.count_eq z
      have c2 := p2.count_eq z
      have c3 := p3.count_eq z
      simp only [List.count_append, List.count_cons, List.count_nil] at c1 c2 c3 ⊢
      omega
    refine Local_decT_mkD 1 _ _ (pickIdxs ((Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false).filter (· != i₁)) Δ.comps ++
      (eraseIdxs (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps).eraseIdx i') [Δ.comps[i₁]] [(eraseIdxs (Δ.edgeIdx (.inr x) .plus false ++ Δ.edgeIdx (.inr x) .minus false) Δ.comps)[i']] []
      [mkC (.G .plus) (liftA 1 Δ.comps[i₁].x) (newA 0)] ps
      [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0)] hperm ?_
      (.cons hM₁ .nil) (Local_pathOK_dPieces _ hps rfl rfl (Local_atX hx1).2 (Local_atX ha1).2)
      (by simp) ?_ (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
    · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsP, hs', Local_strip_dPieces hps, Local_strip_labelQs, List.map_cons, List.map_nil, Local_liftCs_append]
      perm_tac
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with hc
      · subst hc; exact hsx
    · intro c hc pq u hlu
      rw [Local_label_labelQs (fun c hc => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc | hc | hc
          · exact hlP _ c hc
          · exact hlD c hc
          · exact Local_label_dPieces hps c hc
          · subst hc; rfl
          · subst hc; rfl
          ) c hc pq u hlu]
      exact hx1

/-! ### Complex conjugation -/

/-- The component with its kind conjugated. -/
private def Local_conjC {V : Type} (c : Comp V) : Comp V := { c with kind := c.kind.conj }

/-- The blue and red classes exchanged. -/
private def Local_swapM : Option MClass → Option MClass
  | some .plus => some .minus
  | some .minus => some .plus
  | m => m

private theorem Local_mclass_conj (κ : Kind) : κ.conj.mclass = Local_swapM κ.mclass := by
  cases κ with
  | G c => cases c <;> rfl
  | weight c => cases c <;> rfl
  | light c => cases c <;> rfl
  | inv c => cases c <;> rfl
  | wD c d => cases c <;> rfl
  | waved w => cases w <;> rfl
  | aux j r b => cases b <;> rfl
  | _ => rfl

private theorem Local_conj_kinds (κ : Kind) :
    (κ.conj = .dot ↔ κ = .dot) ∧ (κ.conj = .xdot ↔ κ = .xdot) ∧ (κ.conj = .ghost ↔ κ = .ghost) ∧
      κ.conj.joinsMol = κ.joinsMol ∧ κ.conj.isDiffusive = κ.isDiffusive ∧
      κ.conj.isRandom = κ.isRandom ∧ κ.conj.isWeight = κ.isWeight ∧ κ.conj.conj = κ := by
  cases κ with
  | G c => cases c <;> simp [Kind.conj, Charge.flip, Kind.joinsMol, Kind.isDiffusive, Kind.isRandom,
      Kind.isWeight]
  | weight c => cases c <;> simp [Kind.conj, Charge.flip, Kind.joinsMol, Kind.isDiffusive,
      Kind.isRandom, Kind.isWeight]
  | light c => cases c <;> simp [Kind.conj, Charge.flip, Kind.joinsMol, Kind.isDiffusive,
      Kind.isRandom, Kind.isWeight]
  | inv c => cases c <;> simp [Kind.conj, Charge.flip, Kind.joinsMol, Kind.isDiffusive,
      Kind.isRandom, Kind.isWeight]
  | wD c d => cases c <;> simp [Kind.conj, Charge.flip, Kind.joinsMol, Kind.isDiffusive,
      Kind.isRandom, Kind.isWeight]
  | waved w => cases w <;> simp [Kind.conj, Kind.joinsMol, Kind.isDiffusive, Kind.isRandom,
      Kind.isWeight]
  | _ => simp [Kind.conj, Kind.joinsMol, Kind.isDiffusive, Kind.isRandom, Kind.isWeight]

private theorem Local_conj_graphs {k : ℕ} {Δ Δc : Graph k n}
    (h : Δc.comps = Δ.comps.map Local_conjC) :
    Δc.dotGraph = Δ.dotGraph ∧ Δc.molGraph = Δ.molGraph := by
  have key : ∀ (P : Kind → Prop), (∀ κ, P κ.conj ↔ P κ) → ∀ u v,
      (∃ c ∈ Δc.comps, P c.kind ∧ c.x = u ∧ c.y = v) ↔ (∃ c ∈ Δ.comps, P c.kind ∧ c.x = u ∧ c.y = v) := by
    intro P hP u v
    rw [h]
    constructor
    · rintro ⟨c', hc', hp, hx, hy⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
      exact ⟨c, hc, (hP _).1 hp, hx, hy⟩
    · rintro ⟨c, hc, hp, hx, hy⟩
      exact ⟨Local_conjC c, List.mem_map_of_mem hc, (hP _).2 hp, hx, hy⟩
  constructor
  · ext u v
    simp only [Graph.dotGraph, SimpleGraph.fromRel_adj]
    rw [key (fun κ => κ = .dot) (fun κ => (Local_conj_kinds κ).1) u v,
      key (fun κ => κ = .dot) (fun κ => (Local_conj_kinds κ).1) v u]
  · ext u v
    simp only [Graph.molGraph, SimpleGraph.fromRel_adj]
    rw [key (fun κ => κ.joinsMol = true) (fun κ => by rw [(Local_conj_kinds κ).2.2.2.1]) u v,
      key (fun κ => κ.joinsMol = true) (fun κ => by rw [(Local_conj_kinds κ).2.2.2.1]) v u]

private theorem Local_conj_rd {k : ℕ} {Δ Δc : Graph k n} (h : Δc.comps = Δ.comps.map Local_conjC)
    (c : Comp (Atom k n)) :
    Local_rd Δc (Local_conjC c) = (Local_swapM (Local_rd Δ c).1, (Local_rd Δ c).2) := by
  obtain ⟨hd, hm⟩ := Local_conj_graphs h
  have hρ := (Local_graphs_rho hd hm).1
  simp only [Local_rd, Local_conjC, hρ, (Local_conj_kinds c.kind).1, Local_mclass_conj]
  split_ifs <;> rfl

private theorem Local_conj_same {V : Type} {e e' : Local_Ed V} (h : Local_Same e e') :
    Local_Same (Local_swapM e.1, e.2) (Local_swapM e'.1, e'.2) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    simp [Local_swapM, h1, h2]
  · right
    simp only [h1, true_and]
    exact h2

private theorem Local_conjC_map {V W : Type} (f : V → W) (c : Comp V) :
    (Local_conjC c).map f = Local_conjC (c.map f) := rfl

private theorem Local_conjC_solidC {V : Type} [DecidableEq V] (ch : Charge) (a b : V) :
    Local_conjC (solidC ch a b) = solidC ch.flip a b := by
  unfold solidC
  split_ifs <;> rfl

/-- `Local_Dec` under complex conjugation. -/
private theorem Local_dec_conj {Δ Δc : Graph 3 n} {x : Fin n} {j : ℕ} {Δ' Δ'c : Graph 3 (n + j)}
    (h : Δc.comps = Δ.comps.map Local_conjC) (h' : Δ'c.comps = Δ'.comps.map Local_conjC)
    (hd : Local_Dec Δ x j Δ') : Local_Dec Δc x j Δ'c := by
  obtain ⟨K, D, P, R, D', P', N, h1, h2, h3, h4, h5, h6, h7⟩ := hd
  have hfun := Local_graphs_fun (Local_conj_graphs h).1 (Local_conj_graphs h).2
  have hk := Local_conj_kinds
  have hSR : ∀ c c', Local_SameR Δ c c' → Local_SameR Δc (Local_conjC c) (Local_conjC c') := by
    intro c c' hs
    unfold Local_SameR at hs ⊢
    rw [Local_conj_rd h, Local_conj_rd h]
    exact Local_conj_same hs
  refine ⟨K.map Local_conjC, D.map Local_conjC, P.map Local_conjC, R.map Local_conjC,
    D'.map Local_conjC, P'.map Local_conjC, N.map Local_conjC, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h, List.map_map]
    have := h1.map Local_conjC
    simp only [List.map_append, List.map_map] at this
    exact this
  · rw [h', List.map_map]
    have := h2.map Local_conjC
    simp only [List.map_append, List.map_map, liftCs] at this ⊢
    exact this
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine h3.imp fun d d' hm => ?_
    obtain ⟨hkd, hr, hx, hy, hs⟩ := hm
    refine ⟨?_, by simp only [Local_conjC]; rw [(hk _).2.2.2.2.2.1]; exact hr, hx, hy, ?_⟩
    · rcases hkd with hkd | ⟨w1, w2⟩
      · left; simp [Local_conjC, hkd]
      · right; simp only [Local_conjC]; rw [(hk _).2.2.2.2.2.2.1, (hk _).2.2.2.2.2.2.1]
        exact ⟨w1, w2⟩
    · rw [Local_conjC_map]
      exact hSR _ _ hs
  · rcases h4 with ⟨rfl, rfl⟩ | ⟨c, ch, u, v, rfl, hkc, hu, hv, hxu, hxv, hp⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · right
      refine ⟨Local_conjC c, ch.flip, u, v, rfl, ?_, hu, hv, by rw [hfun.2.1]; exact hxu,
        by rw [hfun.2.1]; exact hxv, ?_⟩
      · rcases hkc with hkc | hkc | hkc <;> simp [Local_conjC, hkc, Kind.conj]
      · have := hp.map Local_conjC
        simp only [List.map_cons, List.map_nil, Local_conjC_solidC] at this
        have hw : (Local_conjC c).kind.isWeight = c.kind.isWeight := (hk _).2.2.2.2.2.2.1
        simp only [hw]
        exact this
  · intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    simp only [Local_conjC]
    rw [(hk _).2.2.2.2.2.2.1]
    exact h5 c₀ hc₀
  · intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h6 c₀ hc₀
    refine ⟨a1, a2, fun e => a3 ((hk _).1.1 e), fun e => a4 ((hk _).2.1.1 e),
      fun e => a5 ((hk _).2.2.1.1 e), by simp only [Local_conjC]; rw [(hk _).2.2.2.2.1]; exact a6,
      ?_, fun e => ?_⟩
    · rw [Local_conjC_map, Local_conj_rd h, a7]
      rfl
    · simp only [Local_conjC] at e
      rw [(hk _).2.2.2.1] at e
      rw [hfun.2.1]
      exact a8 e
  · intro i
    rw [(Local_conj_graphs h').2]
    exact h7 i

/-- `Local_DecT` under complex conjugation. -/
private theorem Local_decT_conj {Δ Δc : Graph 3 n} {x : Fin n} {t : Tracked 3 n}
    (h : Δc.comps = Δ.comps.map Local_conjC) (hd : Local_DecT Δ x t) :
    Local_DecT Δc x ⟨t.nOut, t.g.conj, t.f⟩ := by
  obtain ⟨j, hn, hf, hdec, hl⟩ := hd
  obtain ⟨tn, tg, tf⟩ := t
  simp only at hn
  subst hn
  refine ⟨j, rfl, hf, Local_dec_conj h rfl hdec, fun c hc pq u hlu => ?_⟩
  simp only [Graph.conj] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  rw [(Local_graphs_fun (Local_conj_graphs h).1 (Local_conj_graphs h).2).2.1]
  exact hl c₀ hc₀ pq u hlu

end Terms

/-! ## `O_weight` -/

section OWeight

variable {n : ℕ}

private theorem Local_conj_conj_comps {k : ℕ} (Γ : Graph k n) :
    Γ.comps = Γ.conj.comps.map Local_conjC := by
  simp only [Graph.conj, List.map_map]
  conv_lhs => rw [← List.map_id Γ.comps]
  refine List.map_congr_left fun c _ => ?_
  simp [Local_conjC, (Local_conj_kinds c.kind).2.2.2.2.2.2.2]

private theorem Local_conj_labelFree {k : ℕ} {Γ : Graph k n} (h : Γ.LabelFree) :
    Γ.conj.LabelFree := by
  intro c hc
  simp only [Graph.conj] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  exact h c₀ hc₀

/-- **The second step of `O_weight`**: the terms of `O^{(x),2}_weight` of a graph without labels
are good. -/
private theorem Local_oWeight2_good {Γ : Graph 3 n} (hI : Local_Inv Γ) (hlf : Γ.LabelFree)
    (x : Fin n) : ∀ t ∈ oWeight2T (.inr x) Γ, Local_Good Γ (.inr x) t := by
  intro t ht
  unfold oWeight2T at ht
  split_ifs at ht with hp
  · rw [List.mem_singleton] at ht
    subst ht
    exact Local_good_self hI _ rfl
  split at ht
  · rename_i E hE
    exact Local_good_of_decT hI (Local_oW2_decT hlf x hE t ht)
  · split at ht
    · rename_i E _ hE
      unfold TExpansion.conj at ht
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
      exact Local_good_of_decT hI (Local_decT_conj (Local_conj_conj_comps Γ)
        (Local_oW2_decT (Local_conj_labelFree hlf) x hE t₀ ht₀))
    · rw [List.mem_singleton] at ht
      subst ht
      exact Local_good_self hI _ rfl

private theorem Local_oWeight1_labelFree {Γ : Graph 3 n} (hlf : Γ.LabelFree) (x : Atom 3 n) :
    ∀ t ∈ oWeight1T x Γ, t.g.LabelFree := by
  intro t ht
  unfold oWeight1T at ht
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  obtain ⟨K, D, R, D', h1, h2, h3, h4⟩ := Local_splitRegular_dec x Γ.comps p hp
  intro c hc
  have hc' : c ∈ K ++ D' := h2.subset hc
  rcases List.mem_append.1 hc' with hc' | hc'
  · exact hlf c (h1.symm.subset (List.mem_append_left _ (List.mem_append_left _ hc')))
  · obtain ⟨d, -, ⟨ch, -, -, hl, rfl⟩⟩ := Local_f2_right h3 hc'
    exact hl

private theorem Local_good_at {m : ℕ} {u : Atom 3 m} (hu : u.isRight = true)
    (P : Atom 3 m → Prop) (h : ∀ x : Fin m, P (.inr x)) : P u := by
  cases u with
  | inl a => simp at hu
  | inr x => exact h x

/-- **[II, Lemma 5.10] for `O_weight`**: the terms of `O^{(x)}_weight` at an internal atom of a
graph without labels with the invariant are good. -/
private theorem Local_oWeight_good {Γ : Graph 3 n} (hI : Local_Inv Γ) (hlf : Γ.LabelFree)
    (x : Fin n) : ∀ t ∈ oWeightT (.inr x) Γ, Local_Good Γ (.inr x) t := by
  intro t ht
  unfold oWeightT at ht
  split_ifs at ht with hw
  · have h1 : ∀ t ∈ oWeight1T (.inr x) Γ, Local_Good Γ (.inr x) t := Local_oWeight1_good hI x
    have h2 : ∀ t ∈ (oWeight1T (.inr x) Γ).bind (fun f g => oWeight2T (f (.inr x)) g),
        Local_Good Γ (.inr x) t := by
      refine Local_good_bind h1 fun t ht s hs => ?_
      have hlf' := Local_oWeight1_labelFree hlf _ t ht
      obtain ⟨hI', hx', -⟩ := h1 t ht
      exact Local_good_at hx' (fun u => ∀ s ∈ oWeight2T u t.g, Local_Good t.g u s)
        (fun x' => Local_oWeight2_good hI' hlf' x') s hs
    have h3 : ∀ t ∈ ((oWeight1T (.inr x) Γ).bind (fun f g => oWeight2T (f (.inr x)) g)).bind
        (fun _ g => oDotT g), Local_Good Γ (.inr x) t := by
      refine Local_good_bind h2 fun t ht s hs => ?_
      obtain ⟨hI', hx', -⟩ := h2 t ht
      exact Local_oDot_good hI' _ hx' s hs
    refine Local_good_bind h3 (fun t ht s hs => ?_) t ht
    obtain ⟨hI', hx', -⟩ := h3 t ht
    exact Local_good_at hx' (fun u => ∀ s ∈ oWeight1T u t.g, Local_Good t.g u s)
      (fun x' => Local_oWeight1_good hI' x') s hs
  · rw [List.mem_singleton] at ht
    subst ht
    exact Local_good_self hI _ rfl

end OWeight

/-! ## `O_multi-e` and `O_GḠ` -/

section OMultiE

variable {n : ℕ}

private theorem Local_multiEHat_decT {Γ : Graph 3 n} (hlf : Γ.LabelFree) (x : Fin n)
    {E : TExpansion 3 n} (hE : multiEHat (.inr x) Γ = some E) : ∀ t ∈ E, Local_DecT Γ x t := by
  have conjcase : ∀ (O : Atom 3 n → Graph 3 n → Option (TExpansion 3 n)),
      (∀ {Δ : Graph 3 n} {E : TExpansion 3 n}, Δ.LabelFree → O (.inr x) Δ = some E →
        ∀ t ∈ E, Local_DecT Δ x t) →
      (O (.inr x) Γ.conj).map TExpansion.conj = some E → ∀ t ∈ E, Local_DecT Γ x t := by
    intro O hO h t ht
    obtain ⟨E₀, hE₀, rfl⟩ := Option.map_eq_some_iff.1 h
    unfold TExpansion.conj at ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
    exact Local_decT_conj (Local_conj_conj_comps Γ) (hO (Local_conj_labelFree hlf) hE₀ t₀ ht₀)
  unfold multiEHat at hE
  split_ifs at hE
  · exact Local_mEO_decT hlf x hE
  · exact conjcase multiEOut (fun h hE => Local_mEO_decT h x hE) hE
  · exact Local_mEI_decT hlf x hE
  · exact conjcase multiEIn (fun h hE => Local_mEI_decT h x hE) hE

/-- **[II, Lemma 5.10] for `O_multi-e`**: the terms of `O^{(x)}_multi-e` at an internal atom of a
graph without labels with the invariant are good. -/
private theorem Local_oMultiE_good {Γ : Graph 3 n} (hI : Local_Inv Γ) (hlf : Γ.LabelFree)
    (x : Fin n) : ∀ t ∈ oMultiET (.inr x) Γ, Local_Good Γ (.inr x) t := by
  intro t ht
  unfold oMultiET at ht
  split_ifs at ht with hp
  · rw [List.mem_singleton] at ht
    subst ht
    exact Local_good_self hI _ rfl
  split at ht
  · rename_i E hE
    refine Local_good_bind (fun t ht => Local_good_of_decT hI (Local_multiEHat_decT hlf x hE t ht))
      (fun t ht s hs => ?_) t ht
    obtain ⟨hI', hx', -⟩ := Local_good_of_decT hI (Local_multiEHat_decT hlf x hE t ht)
    exact Local_oDot_good hI' _ hx' s hs
  · rw [List.mem_singleton] at ht
    subst ht
    exact Local_good_self hI _ rfl

/-- **[II, Lemma 5.10] for `O_GḠ`**. -/
private theorem Local_oGGbar_good {Γ : Graph 3 n} (hI : Local_Inv Γ) (hlf : Γ.LabelFree)
    (x : Fin n) : ∀ t ∈ oGGbarT (.inr x) Γ, Local_Good Γ (.inr x) t := by
  intro t ht
  unfold oGGbarT at ht
  dsimp only at ht
  split_ifs at ht
  · exact Local_oMultiE_good hI hlf x t ht
  · rw [List.mem_singleton] at ht
    subst ht
    exact Local_good_self hI _ rfl

end OMultiE

/-! ## `O_GG` -/

section OGG

variable {n : ℕ}

local macro "perm_tac" : tactic =>
  `(tactic| (classical
             rw [List.perm_iff_count]
             intro z
             simp only [List.count_append, List.count_cons, List.count_nil]
             omega))

/-- The main term of the `GG` expansion: the solid edges `i` from `x` and `j` into `x` (of one
charge) replaced by a solid edge between their other ends, and a waved edge from `x` to the internal
atom `w`, the other end of one of them; labels only at `w`. -/
private def Local_GM (Δ : Graph 3 n) (x : Fin n) (t : Tracked 3 n) : Prop :=
  ∃ Γ' : Graph 3 n, t = ⟨n, Γ', id⟩ ∧ ∃ (i j : ℕ) (hi : i < Δ.comps.length)
    (hj : j < Δ.comps.length) (ch : Charge) (w : Fin n) (wv : Wave),
    i ≠ j ∧ Δ.comps[i].kind = .G ch ∧ Δ.comps[j].kind = .G ch ∧ Δ.comps[i].x = .inr x ∧
    Δ.comps[j].y = .inr x ∧ (Sum.inr w = Δ.comps[i].y ∨ Sum.inr w = Δ.comps[j].x) ∧
    (Γ'.comps.map Local_stripC).Perm ((eraseIdxs [i, j] Δ.comps).map Local_stripC ++
      [solidC ch Δ.comps[j].x Δ.comps[i].y, mkC (.waved wv) (.inr x) (.inr w)]) ∧
    ∀ c ∈ Γ'.comps, ∀ pq u, c.label = some (pq, u) → u = .inr w

/-- **The `GG` expansion**: the terms of [I, (3.17)] at an internal atom `x` of a graph without
labels whose outgoing solid edge ends at an internal atom: the main terms of `Local_GM`, the other
terms of `Local_Dec`. -/
private theorem Local_ggPos_res {Δ : Graph 3 n} (hlf : Δ.LabelFree) (x : Fin n)
    (hout : Δ.GGOutInt (.inr x)) {E : TExpansion 3 n} (hE : ggPos (.inr x) Δ = some E) :
    ∀ t ∈ E, Local_DecT Δ x t ∨ Local_GM Δ x t := by
  unfold ggPos at hE
  split at hE
  · simp at hE
  split at hE
  · rename_i i j hI hJ
    split at hE
    · rename_i e e' he he'
      dsimp only at hE
      split at hE
      · simp at hE
      obtain rfl := Option.some.inj hE
      have him : i ∈ Δ.edgeIdx (.inr x) .plus true := by rw [hI]; exact List.mem_singleton_self _
      have hjm : j ∈ Δ.edgeIdx (.inr x) .plus false := by rw [hJ]; exact List.mem_singleton_self _
      obtain ⟨hil, hki, hxi, -⟩ := Local_mem_edgeIdx him
      obtain ⟨hxi, hyi⟩ := hxi rfl
      obtain ⟨hjl, hkj, -, hyj⟩ := Local_mem_edgeIdx hjm
      obtain ⟨hyj, hxj⟩ := hyj rfl
      have hij : i ≠ j := by
        rintro rfl
        exact hyi hyj
      have hee : e = Δ.comps[i] := by
        rw [List.getElem?_eq_getElem hil] at he
        exact (Option.some.inj he).symm
      have hee' : e' = Δ.comps[j] := by
        rw [List.getElem?_eq_getElem hjl] at he'
        exact (Option.some.inj he').symm
      subst hee hee'
      obtain ⟨w, hw⟩ : ∃ w, Δ.comps[i].y = .inr w := by
        have := hout _ (List.getElem_mem hil) (by rw [hki]; rfl) hxi
        rcases h : Δ.comps[i].y with a | w
        · rw [h] at this; simp at this
        · exact ⟨w, rfl⟩
      set f := eraseIdxs [i, j] Δ.comps with hf
      have hsΔ : Δ.comps.map Local_stripC = Δ.comps := Local_strip_labelFree hlf
      have hsub : ∀ l : List (Comp (Atom 3 n)), (∀ c ∈ l, c ∈ Δ.comps) → l.map Local_stripC = l :=
        fun l h => Local_strip_labelFree (Γ := ⟨l, 0⟩) fun c hc => hlf c (h c hc)
      have hsΔ' := hsub
      have hlfl : ∀ l : List (Comp (Atom 3 n)), (∀ c ∈ l, c ∈ Δ.comps) → ∀ c ∈ l,
          c.label = none := fun l h c hc => hlf c (h c hc)
      have hsF : f.map Local_stripC = f := hsub _ fun c hc => Local_mem_eraseIdxs hc
      have hlF1 : ∀ c ∈ liftCs 1 f, c.label = none :=
        Local_label_liftCs (hlfl _ fun c hc => Local_mem_eraseIdxs hc)
      have hlF2 : ∀ c ∈ liftCs 2 f, c.label = none :=
        Local_label_liftCs (hlfl _ fun c hc => Local_mem_eraseIdxs hc)
      have hlΔ : ∀ c ∈ liftCs 1 Δ.comps, c.label = none := Local_label_liftCs hlf
      have hx1 : Local_AtX x (liftA 1 (.inr x) : Atom 3 (n + 1)) := Or.inl rfl
      have ha1 : Local_AtX x (newA 0 : Atom 3 (n + 1)) := Or.inr ⟨0, rfl⟩
      have hx2 : Local_AtX x (liftA 2 (.inr x) : Atom 3 (n + 2)) := Or.inl rfl
      have ha2 : Local_AtX x (newA 0 : Atom 3 (n + 2)) := Or.inr ⟨0, rfl⟩
      have hb2 : Local_AtX x (newA 1 : Atom 3 (n + 2)) := Or.inr ⟨1, rfl⟩
      intro t ht
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at ht
      rcases ht with (((((rfl | rfl | rfl | rfl | rfl) | ⟨d', ⟨d, hd, rfl⟩, rfl⟩) |
        ⟨d', ⟨d, hd, rfl⟩, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl)) |
        ⟨d', ⟨d, hd, rfl⟩, rfl⟩) | ⟨d', ⟨d, hd, rfl⟩, rfl⟩
      · right
        exact ⟨_, rfl, i, j, hil, hjl, .plus, w, .plus, hij, hki, hkj, hxi, hyj, Or.inl hw.symm, by
          rw [hf]
          simp only [List.map_append, Local_strip_solidC, Local_strip_mkC, List.map_cons,
            List.map_nil, ← hw, hsΔ' (eraseIdxs [i, j] Δ.comps) (fun c hc => Local_mem_eraseIdxs hc)]
          perm_tac, fun c hc pq u hlu => by
          exfalso
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc
          · rw [hlf c (Local_mem_eraseIdxs hc)] at hlu; simp at hlu
          · subst hc; rw [Local_label_solidC] at hlu; simp at hlu
          · subst hc; simp [mkC] at hlu⟩
      · left
        refine Local_decT_mkD 1 _ _ Δ.comps [] [] [] [] []
          [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0), mkC (.light .plus) (newA 0) (newA 0)]
          (by rw [hsΔ]; simp) ?_ .nil (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
          (Local_m3_1 (w := .s) (by simp)) ?_
        · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsΔ, List.map_cons, List.map_nil]
          perm_tac
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) hx1 ha1
          · subst hc; exact Local_newOK_mkC _ (Or.inr (Or.inl ⟨_, rfl⟩)) ha1 ha1
        · intro c hc pq u hlu
          exfalso
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc
          · rw [hlΔ c hc] at hlu; simp at hlu
          · subst hc; simp [mkC] at hlu
          · subst hc; simp [mkC] at hlu
      · left
        refine Local_decT_mkD 2 _ _ f [Δ.comps[i], Δ.comps[j]] [] []
          [mkC (.G .plus) (newA 0) (liftA 2 Δ.comps[i].y), mkC (.G .plus) (liftA 2 Δ.comps[j].x) (newA 0)] []
          [mkC (.waved .plus) (liftA 2 (.inr x)) (newA 0), mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 1) (newA 1)] (by rw [hsΔ]; simpa using Local_eraseIdxs2_perm Δ.comps i j hil hjl hij) ?_
          (.cons (Local_movR_mk _ _ (by simp [mkC, hki]) (by rw [hki]; rfl)
              (Or.inr ⟨by rw [hxi]; rfl, rfl⟩) (Or.inl rfl)
              (by show Local_proj 2 x (newA 0) = _; rw [Local_proj_new, hxi]) (Local_proj_lift _ _ _)) (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
              (Or.inl rfl) (Or.inr ⟨by rw [hyj]; rfl, rfl⟩)
              (Local_proj_lift _ _ _) (by show Local_proj 2 x (newA 0) = _; rw [Local_proj_new, hyj])) .nil)) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
          (Local_m3_2 (w := .plus) (w' := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
        · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsF, Local_strip_labelQs, List.map_cons, List.map_nil]
          perm_tac
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) hx2 ha2
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) ha2 hb2
          · subst hc; exact Local_newOK_mkC _ (Or.inr (Or.inl ⟨_, rfl⟩)) hb2 hb2
        · intro c hc pq u hlu
          exfalso
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc | hc | hc | hc
          · rw [hlF2 c hc] at hlu; simp at hlu
          · subst hc; simp [mkC] at hlu
          · subst hc; simp [mkC] at hlu
          · subst hc; simp [mkC] at hlu
          · subst hc; simp [mkC] at hlu
          · subst hc; simp [mkC] at hlu
      · left
        refine Local_decT_mkD 1 _ _ f [Δ.comps[i], Δ.comps[j]] [] []
          [mkC (.G .plus) (newA 0) (liftA 1 Δ.comps[i].y), mkC (.G .plus) (liftA 1 Δ.comps[j].x) (newA 0)] []
          [mkC (.light .plus) (liftA 1 (.inr x)) (liftA 1 (.inr x)), mkC (.waved .s) (liftA 1 (.inr x)) (newA 0)] (by rw [hsΔ]; simpa using Local_eraseIdxs2_perm Δ.comps i j hil hjl hij) ?_
          (.cons (Local_movR_mk _ _ (by simp [mkC, hki]) (by rw [hki]; rfl)
              (Or.inr ⟨by rw [hxi]; rfl, rfl⟩) (Or.inl rfl)
              (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hxi]) (Local_proj_lift _ _ _)) (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
              (Or.inl rfl) (Or.inr ⟨by rw [hyj]; rfl, rfl⟩)
              (Local_proj_lift _ _ _) (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hyj])) .nil)) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
          (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
        · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsF, Local_strip_labelQs, List.map_cons, List.map_nil]
          perm_tac
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc
          · subst hc; exact Local_newOK_mkC _ (Or.inr (Or.inl ⟨_, rfl⟩)) hx1 hx1
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) hx1 ha1
        · intro c hc pq u hlu
          exfalso
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc | hc | hc
          · rw [hlF1 c hc] at hlu; simp at hlu
          · subst hc; simp [mkC] at hlu
          · subst hc; simp [mkC] at hlu
          · subst hc; simp [mkC] at hlu
          · subst hc; simp [mkC] at hlu
      · left
        refine Local_decT_mkD 2 _ _ f [Δ.comps[i], Δ.comps[j]] [] []
          [mkC (.G .plus) (newA 1) (liftA 2 Δ.comps[i].y), mkC (.G .plus) (liftA 2 Δ.comps[j].x) (newA 1)] []
          [mkC (.waved .plus) (liftA 2 (.inr x)) (newA 0), mkC (.waved .s) (newA 0) (newA 1), mkC (.light .plus) (newA 0) (newA 0)] (by rw [hsΔ]; simpa using Local_eraseIdxs2_perm Δ.comps i j hil hjl hij) ?_
          (.cons (Local_movR_mk _ _ (by simp [mkC, hki]) (by rw [hki]; rfl)
              (Or.inr ⟨by rw [hxi]; rfl, rfl⟩) (Or.inl rfl)
              (by show Local_proj 2 x (newA 1) = _; rw [Local_proj_new, hxi]) (Local_proj_lift _ _ _)) (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
              (Or.inl rfl) (Or.inr ⟨by rw [hyj]; rfl, rfl⟩)
              (Local_proj_lift _ _ _) (by show Local_proj 2 x (newA 1) = _; rw [Local_proj_new, hyj])) .nil)) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
          (Local_m3_2 (w := .plus) (w' := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
        · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsF, Local_strip_labelQs, List.map_cons, List.map_nil]
          perm_tac
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) hx2 ha2
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) ha2 hb2
          · subst hc; exact Local_newOK_mkC _ (Or.inr (Or.inl ⟨_, rfl⟩)) ha2 ha2
        · intro c hc pq u hlu
          exfalso
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc | hc | hc | hc
          · rw [hlF2 c hc] at hlu; simp at hlu
          · subst hc; simp [mkC] at hlu
          · subst hc; simp [mkC] at hlu
          · subst hc; simp [mkC] at hlu
          · subst hc; simp [mkC] at hlu
          · subst hc; simp [mkC] at hlu
      · left
        obtain ⟨i', hi', ps, hps, rfl, hpf⟩ := Local_dTerms_lift hd
        have hs' : (f.eraseIdx i').map Local_stripC = f.eraseIdx i' :=
          hsub _ fun c hc => Local_mem_eraseIdxs (List.mem_of_mem_eraseIdx hc)
        have hlD : ∀ c ∈ liftCs 1 (f.eraseIdx i'), c.label = none :=
          Local_label_liftCs (hlfl _ fun c hc => Local_mem_eraseIdxs (List.mem_of_mem_eraseIdx hc))
        have hperm : (Δ.comps.map Local_stripC).Perm (f.eraseIdx i' ++ [Δ.comps[i], Δ.comps[j]] ++
            [f[i']] ++ []) := by
          rw [hsΔ]
          have p1 := Local_eraseIdxs2_perm Δ.comps i j hil hjl hij
          rw [← hf] at p1
          have p3 := hpf
          classical
          rw [List.perm_iff_count]
          intro z
          have c1 := p1.count_eq z
          have c3 := p3.count_eq z
          simp only [List.count_append, List.count_cons, List.count_nil] at c1 c3 ⊢
          omega
        refine Local_decT_mkD 1 _ _ (f.eraseIdx i') [Δ.comps[i], Δ.comps[j]] [f[i']] []
          [mkC (.G .plus) (newA 0) (liftA 1 Δ.comps[i].y), mkC (.G .plus) (liftA 1 Δ.comps[j].x) (liftA 1 (.inr x))] ps
          [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0)] hperm ?_
          (.cons (Local_movR_mk _ _ (by simp [mkC, hki]) (by rw [hki]; rfl)
              (Or.inr ⟨by rw [hxi]; rfl, rfl⟩) (Or.inl rfl)
              (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hxi]) (Local_proj_lift _ _ _)) (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
              (Or.inl rfl) (Or.inl (by rw [hyj]; rfl))
              (Local_proj_lift _ _ _) (by show Local_proj 1 x (liftA 1 (.inr x)) = _; rw [Local_proj_lift, hyj])) .nil)) (Local_pathOK_dPieces _ hps rfl rfl (Local_atX ha1).2 (Local_atX hx1).2) (by simp) ?_
          (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
        · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hs', Local_strip_labelQs, List.map_cons, List.map_nil, Local_strip_dPieces hps, Local_liftCs_append]
          perm_tac
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) hx1 ha1
        · intro c hc pq u hlu
          exfalso
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc | hc | hc
          · rw [hlD c hc] at hlu; simp at hlu
          · rw [Local_label_dPieces hps c hc] at hlu; simp at hlu
          · subst hc; simp [mkC] at hlu
          · subst hc; simp [mkC] at hlu
          · subst hc; simp [mkC] at hlu
      · left
        obtain ⟨i', hi', ps, hps, rfl, hpf⟩ := Local_dTerms_lift hd
        have hs' : (f.eraseIdx i').map Local_stripC = f.eraseIdx i' :=
          hsub _ fun c hc => Local_mem_eraseIdxs (List.mem_of_mem_eraseIdx hc)
        have hlD : ∀ c ∈ liftCs 2 (f.eraseIdx i'), c.label = none :=
          Local_label_liftCs (hlfl _ fun c hc => Local_mem_eraseIdxs (List.mem_of_mem_eraseIdx hc))
        have hperm : (Δ.comps.map Local_stripC).Perm (f.eraseIdx i' ++ [Δ.comps[i], Δ.comps[j]] ++
            [f[i']] ++ []) := by
          rw [hsΔ]
          have p1 := Local_eraseIdxs2_perm Δ.comps i j hil hjl hij
          rw [← hf] at p1
          have p3 := hpf
          classical
          rw [List.perm_iff_count]
          intro z
          have c1 := p1.count_eq z
          have c3 := p3.count_eq z
          simp only [List.count_append, List.count_cons, List.count_nil] at c1 c3 ⊢
          omega
        refine Local_decT_mkD 2 _ _ (f.eraseIdx i') [Δ.comps[i], Δ.comps[j]] [f[i']] []
          [mkC (.G .plus) (newA 1) (liftA 2 Δ.comps[i].y), mkC (.G .plus) (liftA 2 Δ.comps[j].x) (newA 0)] ps
          [mkC (.waved .plus) (liftA 2 (.inr x)) (newA 0), mkC (.waved .s) (newA 0) (newA 1)] hperm ?_
          (.cons (Local_movR_mk _ _ (by simp [mkC, hki]) (by rw [hki]; rfl)
              (Or.inr ⟨by rw [hxi]; rfl, rfl⟩) (Or.inl rfl)
              (by show Local_proj 2 x (newA 1) = _; rw [Local_proj_new, hxi]) (Local_proj_lift _ _ _)) (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
              (Or.inl rfl) (Or.inr ⟨by rw [hyj]; rfl, rfl⟩)
              (Local_proj_lift _ _ _) (by show Local_proj 2 x (newA 0) = _; rw [Local_proj_new, hyj])) .nil)) (Local_pathOK_dPieces _ hps rfl rfl (Local_atX hb2).2 (Local_atX ha2).2) (by simp) ?_
          (Local_m3_2 (w := .plus) (w' := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
        · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hs', Local_strip_labelQs, List.map_cons, List.map_nil, Local_strip_dPieces hps, Local_liftCs_append]
          perm_tac
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) hx2 ha2
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) ha2 hb2
        · intro c hc pq u hlu
          exfalso
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc | hc | hc | hc
          · rw [hlD c hc] at hlu; simp at hlu
          · rw [Local_label_dPieces hps c hc] at hlu; simp at hlu
          · subst hc; simp [mkC] at hlu
          · subst hc; simp [mkC] at hlu
          · subst hc; simp [mkC] at hlu
          · subst hc; simp [mkC] at hlu
      · left
        refine Local_decT_mk0 _ _ (by rw [Local_strip_labelQs]) ?_
        intro c hc pq u hlu
        exact Local_label_labelQs (fun c hc => hlf c hc) c hc pq u hlu
      · left
        refine Local_decT_mkD 1 _ _ f [Δ.comps[i], Δ.comps[j]] [] []
          [mkC (.G .plus) (newA 0) (liftA 1 Δ.comps[i].y), mkC (.G .plus) (liftA 1 Δ.comps[j].x) (newA 0)] []
          [mkC (.waved .plus) (liftA 1 (.inr x)) (newA 0)] (by rw [hsΔ]; simpa using Local_eraseIdxs2_perm Δ.comps i j hil hjl hij) ?_
          (.cons (Local_movR_mk _ _ (by simp [mkC, hki]) (by rw [hki]; rfl)
              (Or.inr ⟨by rw [hxi]; rfl, rfl⟩) (Or.inl rfl)
              (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hxi]) (Local_proj_lift _ _ _)) (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
              (Or.inl rfl) (Or.inr ⟨by rw [hyj]; rfl, rfl⟩)
              (Local_proj_lift _ _ _) (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hyj])) .nil)) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
          (Local_m3_1 (w := .plus) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
        · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsF, Local_strip_labelQs, List.map_cons, List.map_nil]
          perm_tac
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) hx1 ha1
        · intro c hc pq u hlu
          rcases List.mem_append.1 hc with hc | hc
          · rw [Local_label_labelQs (fun c hc => by
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
              rcases hc with hc | hc | hc
              · exact hlF1 c hc
              · subst hc; rfl
              · subst hc; rfl
              ) c hc pq u hlu]
            exact ha1
          · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
            rcases hc with hc
            · subst hc; simp [mkC] at hlu
      · right
        exact ⟨_, rfl, i, j, hil, hjl, .plus, w, .plus, hij, hki, hkj, hxi, hyj, Or.inl hw.symm, by
          rw [hf]
          simp only [List.map_append, Local_strip_labelQs, Local_strip_solidC, Local_strip_mkC,
            List.map_cons, List.map_nil, ← hw,
            hsΔ' (eraseIdxs [i, j] Δ.comps) (fun c hc => Local_mem_eraseIdxs hc)]
          perm_tac, fun c hc pq u hlu => by
          rcases List.mem_append.1 hc with hc | hc
          · rw [Local_label_labelQs (fun c hc => by
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
              rcases hc with hc | hc
              · exact hlf c (Local_mem_eraseIdxs hc)
              · subst hc; exact Local_label_solidC _ _ _) c hc pq u hlu]
            exact hw
          · simp only [List.mem_singleton] at hc
            subst hc; simp [mkC] at hlu⟩
      · left
        refine Local_decT_mkD 1 _ _ Δ.comps [] [] [] [] []
          [mkC (.light .plus) (newA 0) (newA 0), mkC (.waved .s) (liftA 1 (.inr x)) (newA 0)]
          (by rw [hsΔ]; simp) ?_ .nil (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
          (Local_m3_1 (w := .s) (by simp)) ?_
        · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsΔ, Local_strip_labelQs,
            List.map_cons, List.map_nil]
          perm_tac
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc
          · subst hc; exact Local_newOK_mkC _ (Or.inr (Or.inl ⟨_, rfl⟩)) ha1 ha1
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) hx1 ha1
        · intro c hc pq u hlu
          rcases List.mem_append.1 hc with hc | hc
          · rw [Local_label_labelQs (fun c hc => by
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
              rcases hc with hc | hc
              · exact hlΔ c hc
              · subst hc; rfl
              ) c hc pq u hlu]
            exact hx1
          · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
            rcases hc with hc
            · subst hc; simp [mkC] at hlu
      · left
        refine Local_decT_mkD 2 _ _ f [Δ.comps[i], Δ.comps[j]] [] []
          [mkC (.G .plus) (newA 0) (liftA 2 Δ.comps[i].y), mkC (.G .plus) (liftA 2 Δ.comps[j].x) (newA 0)] []
          [mkC (.light .plus) (newA 1) (newA 1), mkC (.waved .plus) (liftA 2 (.inr x)) (newA 0), mkC (.waved .s) (newA 0) (newA 1)] (by rw [hsΔ]; simpa using Local_eraseIdxs2_perm Δ.comps i j hil hjl hij) ?_
          (.cons (Local_movR_mk _ _ (by simp [mkC, hki]) (by rw [hki]; rfl)
              (Or.inr ⟨by rw [hxi]; rfl, rfl⟩) (Or.inl rfl)
              (by show Local_proj 2 x (newA 0) = _; rw [Local_proj_new, hxi]) (Local_proj_lift _ _ _)) (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
              (Or.inl rfl) (Or.inr ⟨by rw [hyj]; rfl, rfl⟩)
              (Local_proj_lift _ _ _) (by show Local_proj 2 x (newA 0) = _; rw [Local_proj_new, hyj])) .nil)) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
          (Local_m3_2 (w := .plus) (w' := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
        · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsF, Local_strip_labelQs, List.map_cons, List.map_nil]
          perm_tac
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc
          · subst hc; exact Local_newOK_mkC _ (Or.inr (Or.inl ⟨_, rfl⟩)) hb2 hb2
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) hx2 ha2
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) ha2 hb2
        · intro c hc pq u hlu
          rcases List.mem_append.1 hc with hc | hc
          · rw [Local_label_labelQs (fun c hc => by
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
              rcases hc with hc | hc | hc | hc
              · exact hlF2 c hc
              · subst hc; rfl
              · subst hc; rfl
              · subst hc; rfl
              ) c hc pq u hlu]
            exact ha2
          · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
            rcases hc with hc | hc
            · subst hc; simp [mkC] at hlu
            · subst hc; simp [mkC] at hlu
      · left
        refine Local_decT_mkD 1 _ _ f [Δ.comps[i], Δ.comps[j]] [] []
          [mkC (.G .plus) (newA 0) (liftA 1 Δ.comps[i].y), mkC (.G .plus) (liftA 1 Δ.comps[j].x) (newA 0)] []
          [mkC (.weight .plus) (liftA 1 (.inr x)) (liftA 1 (.inr x)), mkC (.waved .s) (liftA 1 (.inr x)) (newA 0)] (by rw [hsΔ]; simpa using Local_eraseIdxs2_perm Δ.comps i j hil hjl hij) ?_
          (.cons (Local_movR_mk _ _ (by simp [mkC, hki]) (by rw [hki]; rfl)
              (Or.inr ⟨by rw [hxi]; rfl, rfl⟩) (Or.inl rfl)
              (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hxi]) (Local_proj_lift _ _ _)) (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
              (Or.inl rfl) (Or.inr ⟨by rw [hyj]; rfl, rfl⟩)
              (Local_proj_lift _ _ _) (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hyj])) .nil)) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
          (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
        · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsF, Local_strip_labelQs, List.map_cons, List.map_nil]
          perm_tac
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc
          · subst hc; exact Local_newOK_mkC _ (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))) hx1 hx1
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) hx1 ha1
        · intro c hc pq u hlu
          rcases List.mem_append.1 hc with hc | hc
          · rw [Local_label_labelQs (fun c hc => by
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
              rcases hc with hc | hc | hc | hc
              · exact hlF1 c hc
              · subst hc; rfl
              · subst hc; rfl
              · subst hc; rfl
              ) c hc pq u hlu]
            exact hx1
          · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
            rcases hc with hc
            · subst hc; simp [mkC] at hlu
      · left
        refine Local_decT_mkD 2 _ _ f [Δ.comps[i], Δ.comps[j]] [] []
          [mkC (.G .plus) (newA 1) (liftA 2 Δ.comps[i].y), mkC (.G .plus) (liftA 2 Δ.comps[j].x) (newA 1)] []
          [mkC (.weight .plus) (newA 0) (newA 0), mkC (.waved .plus) (liftA 2 (.inr x)) (newA 0), mkC (.waved .s) (newA 0) (newA 1)] (by rw [hsΔ]; simpa using Local_eraseIdxs2_perm Δ.comps i j hil hjl hij) ?_
          (.cons (Local_movR_mk _ _ (by simp [mkC, hki]) (by rw [hki]; rfl)
              (Or.inr ⟨by rw [hxi]; rfl, rfl⟩) (Or.inl rfl)
              (by show Local_proj 2 x (newA 1) = _; rw [Local_proj_new, hxi]) (Local_proj_lift _ _ _)) (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
              (Or.inl rfl) (Or.inr ⟨by rw [hyj]; rfl, rfl⟩)
              (Local_proj_lift _ _ _) (by show Local_proj 2 x (newA 1) = _; rw [Local_proj_new, hyj])) .nil)) (Or.inl ⟨rfl, rfl⟩) (by simp) ?_
          (Local_m3_2 (w := .plus) (w' := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
        · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hsF, Local_strip_labelQs, List.map_cons, List.map_nil]
          perm_tac
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc | hc
          · subst hc; exact Local_newOK_mkC _ (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))) ha2 ha2
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) hx2 ha2
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) ha2 hb2
        · intro c hc pq u hlu
          rcases List.mem_append.1 hc with hc | hc
          · rw [Local_label_labelQs (fun c hc => by
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
              rcases hc with hc | hc | hc | hc
              · exact hlF2 c hc
              · subst hc; rfl
              · subst hc; rfl
              · subst hc; rfl
              ) c hc pq u hlu]
            exact ha2
          · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
            rcases hc with hc | hc
            · subst hc; simp [mkC] at hlu
            · subst hc; simp [mkC] at hlu
      · left
        obtain ⟨i', hi', ps, hps, rfl, hpf⟩ := Local_dTerms_lift hd
        have hs' : (f.eraseIdx i').map Local_stripC = f.eraseIdx i' :=
          hsub _ fun c hc => Local_mem_eraseIdxs (List.mem_of_mem_eraseIdx hc)
        have hlD : ∀ c ∈ liftCs 1 (f.eraseIdx i'), c.label = none :=
          Local_label_liftCs (hlfl _ fun c hc => Local_mem_eraseIdxs (List.mem_of_mem_eraseIdx hc))
        have hperm : (Δ.comps.map Local_stripC).Perm (f.eraseIdx i' ++ [Δ.comps[i], Δ.comps[j]] ++
            [f[i']] ++ []) := by
          rw [hsΔ]
          have p1 := Local_eraseIdxs2_perm Δ.comps i j hil hjl hij
          rw [← hf] at p1
          have p3 := hpf
          classical
          rw [List.perm_iff_count]
          intro z
          have c1 := p1.count_eq z
          have c3 := p3.count_eq z
          simp only [List.count_append, List.count_cons, List.count_nil] at c1 c3 ⊢
          omega
        refine Local_decT_mkD 1 _ _ (f.eraseIdx i') [Δ.comps[i], Δ.comps[j]] [f[i']] []
          [mkC (.G .plus) (newA 0) (liftA 1 Δ.comps[i].y), mkC (.G .plus) (liftA 1 Δ.comps[j].x) (liftA 1 (.inr x))] ps
          [mkC (.waved .s) (liftA 1 (.inr x)) (newA 0)] hperm ?_
          (.cons (Local_movR_mk _ _ (by simp [mkC, hki]) (by rw [hki]; rfl)
              (Or.inr ⟨by rw [hxi]; rfl, rfl⟩) (Or.inl rfl)
              (by show Local_proj 1 x (newA 0) = _; rw [Local_proj_new, hxi]) (Local_proj_lift _ _ _)) (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
              (Or.inl rfl) (Or.inl (by rw [hyj]; rfl))
              (Local_proj_lift _ _ _) (by show Local_proj 1 x (liftA 1 (.inr x)) = _; rw [Local_proj_lift, hyj])) .nil)) (Local_pathOK_dPieces _ hps rfl rfl (Local_atX ha1).2 (Local_atX hx1).2) (by simp) ?_
          (Local_m3_1 (w := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
        · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hs', Local_strip_labelQs, List.map_cons, List.map_nil, Local_strip_dPieces hps, Local_liftCs_append]
          perm_tac
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) hx1 ha1
        · intro c hc pq u hlu
          rcases List.mem_append.1 hc with hc | hc
          · rw [Local_label_labelQs (fun c hc => by
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
              rcases hc with hc | hc | hc | hc
              · exact hlD c hc
              · exact Local_label_dPieces hps c hc
              · subst hc; rfl
              · subst hc; rfl
              ) c hc pq u hlu]
            exact hx1
          · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
            rcases hc with hc
            · subst hc; simp [mkC] at hlu
      · left
        obtain ⟨i', hi', ps, hps, rfl, hpf⟩ := Local_dTerms_lift hd
        have hs' : (f.eraseIdx i').map Local_stripC = f.eraseIdx i' :=
          hsub _ fun c hc => Local_mem_eraseIdxs (List.mem_of_mem_eraseIdx hc)
        have hlD : ∀ c ∈ liftCs 2 (f.eraseIdx i'), c.label = none :=
          Local_label_liftCs (hlfl _ fun c hc => Local_mem_eraseIdxs (List.mem_of_mem_eraseIdx hc))
        have hperm : (Δ.comps.map Local_stripC).Perm (f.eraseIdx i' ++ [Δ.comps[i], Δ.comps[j]] ++
            [f[i']] ++ []) := by
          rw [hsΔ]
          have p1 := Local_eraseIdxs2_perm Δ.comps i j hil hjl hij
          rw [← hf] at p1
          have p3 := hpf
          classical
          rw [List.perm_iff_count]
          intro z
          have c1 := p1.count_eq z
          have c3 := p3.count_eq z
          simp only [List.count_append, List.count_cons, List.count_nil] at c1 c3 ⊢
          omega
        refine Local_decT_mkD 2 _ _ (f.eraseIdx i') [Δ.comps[i], Δ.comps[j]] [f[i']] []
          [mkC (.G .plus) (newA 1) (liftA 2 Δ.comps[i].y), mkC (.G .plus) (liftA 2 Δ.comps[j].x) (newA 0)] ps
          [mkC (.waved .plus) (liftA 2 (.inr x)) (newA 0), mkC (.waved .s) (newA 0) (newA 1)] hperm ?_
          (.cons (Local_movR_mk _ _ (by simp [mkC, hki]) (by rw [hki]; rfl)
              (Or.inr ⟨by rw [hxi]; rfl, rfl⟩) (Or.inl rfl)
              (by show Local_proj 2 x (newA 1) = _; rw [Local_proj_new, hxi]) (Local_proj_lift _ _ _)) (.cons (Local_movR_mk _ _ (by simp [mkC, hkj]) (by rw [hkj]; rfl)
              (Or.inl rfl) (Or.inr ⟨by rw [hyj]; rfl, rfl⟩)
              (Local_proj_lift _ _ _) (by show Local_proj 2 x (newA 0) = _; rw [Local_proj_new, hyj])) .nil)) (Local_pathOK_dPieces _ hps rfl rfl (Local_atX hb2).2 (Local_atX ha2).2) (by simp) ?_
          (Local_m3_2 (w := .plus) (w' := .s) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp) (by first | exact Local_mem_labelQs_nr (by simp) rfl | simp)) ?_
        · simp only [List.map_append, Local_strip_liftCs, Local_strip_mkC, hs', Local_strip_labelQs, List.map_cons, List.map_nil, Local_strip_dPieces hps, Local_liftCs_append]
          perm_tac
        · intro c hc
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
          rcases hc with hc | hc
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) hx2 ha2
          · subst hc; exact Local_newOK_mkC _ (Or.inl ⟨_, rfl⟩) ha2 hb2
        · intro c hc pq u hlu
          rcases List.mem_append.1 hc with hc | hc
          · rw [Local_label_labelQs (fun c hc => by
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
              rcases hc with hc | hc | hc | hc
              · exact hlD c hc
              · exact Local_label_dPieces hps c hc
              · subst hc; rfl
              · subst hc; rfl
              ) c hc pq u hlu]
            exact ha2
          · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
            rcases hc with hc | hc
            · subst hc; simp [mkC] at hlu
            · subst hc; simp [mkC] at hlu
    · simp at hE
  · simp at hE

/-! ### The main term of the `GG` expansion -/

private theorem Local_dot_fun {k : ℕ} {Γ Γ' : Graph k n} (hd : Γ'.dotGraph = Γ.dotGraph) :
    Γ'.SameBlock = Γ.SameBlock ∧ Γ'.flatAtom = Γ.flatAtom ∧ Γ'.Unpinned = Γ.Unpinned := by
  have hb : Γ'.SameBlock = Γ.SameBlock := by
    funext u v
    unfold Graph.SameBlock
    rw [hd]
  have ha : Γ'.anchor = Γ.anchor := by
    funext u
    unfold Graph.anchor
    simp only [hb]
  refine ⟨hb, ?_, ?_⟩
  · funext u
    cases u with
    | inl a => simp only [Graph.flatAtom, ha]
    | inr a => rfl
  · funext u
    unfold Graph.Unpinned
    rw [hb]

private theorem Local_mol_fun {k : ℕ} {Γ Γ' : Graph k n} (hm : Γ'.molGraph = Γ.molGraph) :
    Γ'.molRep = Γ.molRep := by
  have hM : Γ'.SameMol = Γ.SameMol := by
    funext u v
    unfold Graph.SameMol
    rw [hm]
  funext u
  cases u with
  | inl a => rfl
  | inr a => simp only [Graph.molRep, hM]

private theorem Local_pin_unp {k : ℕ} {Γ : Graph k n} {a : Fin k} (h : Γ.Unpinned (.inl a)) :
    Local_pin Γ a = (none, .inl a, .inl a) := by
  have hA : Γ.anchor (.inl a) = none := Local_anchor_none.2 h.2
  simp only [Local_pin, hA]

private theorem Local_pin_pin {k : ℕ} {Γ : Graph k n} {a : Fin k} (h : ¬ Γ.Unpinned (.inl a)) :
    Local_pin Γ a = (some (pinClass a), Local_rho Γ (.inl a), .inl a) := by
  rcases hA : Γ.anchor (.inl a) with _ | b
  · exact absurd ⟨rfl, Local_anchor_none.1 hA⟩ h
  · simp only [Local_pin, Local_rho, Graph.flatAtom, hA]

private theorem Local_fromRel_congr {V : Type} {l l' : List (Comp V)} (P : Kind → Prop)
    (h : ∀ u v, (∃ c ∈ l, P c.kind ∧ c.x = u ∧ c.y = v) ↔
      (∃ c ∈ l', P c.kind ∧ c.x = u ∧ c.y = v)) :
    (SimpleGraph.fromRel fun u v => ∃ c ∈ l, P c.kind ∧ c.x = u ∧ c.y = v) =
      SimpleGraph.fromRel fun u v => ∃ c ∈ l', P c.kind ∧ c.x = u ∧ c.y = v := by
  ext u v
  simp only [SimpleGraph.fromRel_adj, h]

/-- A dotted edge `x = w` and a waved edge between the internal atoms `x` and `w` give the same
reading. -/
private theorem Local_dotWaved {Δ Γ₀ : Graph 3 n} {x w : Fin n}
    (hd : Γ₀.dotGraph = Δ.dotGraph)
    (hm : Γ₀.molGraph = (Local_addG Δ (.inr x) (.inr w)).molGraph) :
    Local_rho Γ₀ = Local_rho (Local_addG Δ (.inr x) (.inr w)) ∧
      Local_pin Γ₀ = Local_pin (Local_addG Δ (.inr x) (.inr w)) ∧
      Γ₀.toMG'.int = (Local_addG Δ (.inr x) (.inr w)).toMG'.int := by
  obtain ⟨-, hf, hu⟩ := Local_dot_fun hd
  have hr := Local_mol_fun hm
  have hp : Δ.SameBlock (.inr x) (.inr x) := SimpleGraph.Reachable.refl _
  have hρ : Local_rho Γ₀ = Local_rho (Local_addG Δ (.inr x) (.inr w)) := by
    funext u
    rw [Local_add_rho (u := u) hp (fun h => h.1.2 w h.2)]
    simp only [Local_rho]
    rw [Local_add_molRep_molRep, hf, hr]
  refine ⟨hρ, ?_, ?_⟩
  · funext a
    by_cases h : Δ.Unpinned (.inl a)
    · rw [Local_pin_unp (show Γ₀.Unpinned (.inl a) by rw [hu]; exact h),
        Local_pin_unp (Local_add_unpinned hp h (h.2 w))]
    · rw [Local_pin_pin (show ¬ Γ₀.Unpinned (.inl a) by rw [hu]; exact h),
        Local_pin_pin (fun h' => h (Local_add_unpinned_of h')), hρ]
  · simp only [Graph.toMG', hr]

private theorem Local_RG_congr {k : ℕ} {Γ Γ' : Graph k n} (L : List (Comp (Atom k n)))
    (hρ : Local_rho Γ' = Local_rho Γ) (hp : Local_pin Γ' = Local_pin Γ)
    (hi : Γ'.toMG'.int = Γ.toMG'.int) :
    Local_Carry (Local_RG Γ L) (Local_RG Γ' L) id := by
  have hrd : Local_rd Γ' = Local_rd Γ := by
    funext c
    simp only [Local_rd, hρ]
  have he : Γ'.toMG'.ext = Γ.toMG'.ext := rfl
  unfold Local_RG
  rw [hi, hp, hrd, he]
  exact Local_carry_refl _

private theorem Local_solidC_xy {V : Type} [DecidableEq V] (ch : Charge) (a b : V) :
    (solidC ch a b).x = a ∧ (solidC ch a b).y = b := by
  unfold solidC
  split_ifs with h
  · subst h
    exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

private theorem Local_rd_solidC' {k : ℕ} (Γ : Graph k n) (ch : Charge) (a b : Atom k n) :
    Local_rd Γ (solidC ch a b) = Local_rd Γ (mkC (.G ch) a b) := by
  unfold solidC
  split_ifs with h
  · subst h
    simp [Local_rd, mkC]
  · rfl

private theorem Local_countP_le2 {α : Type*} (p : α → Bool) (F : List α) (a b c d : α)
    (hb : p b = false) (h : p a = true → p c = true ∨ p d = true) :
    (F ++ [a, b]).countP p ≤ (F ++ [c, d]).countP p := by
  simp only [List.countP_append, List.countP_cons, List.countP_nil, hb]
  cases hpa : p a <;> cases hpc : p c <;> cases hpd : p d <;> simp_all

set_option maxHeartbeats 400000 in
/-- **The main term of the `GG` expansion is good**: the solid edges `x → y` and `y' → x` replaced
by a solid edge `y' → y` and a waved edge from `x` to `w ∈ {y, y'}`, on a graph without labels with
the invariant. It is read as the graph with the dotted edge `x = w` added, and the edge between
the molecule of `x` and the other end. -/
private theorem Local_good_of_GM {Δ : Graph 3 n} (hI : Local_Inv Δ) (hlf : Δ.LabelFree) {x : Fin n}
    {t : Tracked 3 n} (h : Local_GM Δ x t) : Local_Good Δ (.inr x) t := by
  obtain ⟨Γ', rfl, i, j, hi, hj, ch, w, wv, hij, hki, hkj, hxi, hyj, hw, hperm, hlab⟩ := h
  have hI' := hI
  obtain ⟨hs, hC, hE, hG⟩ := hI
  have hf : (eraseIdxs [i, j] Δ.comps).map Local_stripC = eraseIdxs [i, j] Δ.comps :=
    Local_strip_labelFree (Γ := ⟨_, 0⟩) fun c hc => hlf c (Local_mem_eraseIdxs hc)
  rw [hf] at hperm
  have hΔ := Local_eraseIdxs2_perm Δ.comps i j hi hj hij
  generalize eraseIdxs [i, j] Δ.comps = F at hΔ hperm
  generalize Δ.comps[i] = e at hΔ hki hxi hw hperm
  generalize Δ.comps[j] = e' at hΔ hkj hyj hw hperm
  obtain ⟨hsx, hsy⟩ := Local_solidC_xy ch e'.x e.y
  have hks := Local_kind_solidC ch e'.x e.y
  have memΔ : ∀ c, c ∈ Δ.comps ↔ c ∈ F ∨ c = e ∨ c = e' := by
    intro c
    rw [hΔ.mem_iff]
    simp
  let Γ₀ : Graph 3 n := ⟨F ++ [solidC ch e'.x e.y, mkC (.waved wv) (.inr x) (.inr w)], Γ'.coeff⟩
  have memΓ₀ : ∀ c, c ∈ Γ₀.comps ↔ c ∈ F ∨ c = solidC ch e'.x e.y ∨
      c = mkC (.waved wv) (.inr x) (.inr w) := by
    intro c
    show c ∈ F ++ [_, _] ↔ _
    simp
  have memD : ∀ c, c ∈ (Local_addG Δ (.inr x) (.inr w)).comps ↔ c ∈ Δ.comps ∨
      c = mkC .dot (.inr x) (.inr w) := by
    intro c
    show c ∈ Δ.comps ++ [_] ↔ _
    simp
  have hS : Local_Same3 Γ₀ Γ' := by
    unfold Local_Same3
    have e1 : Γ'.comps.map Local_tri = (Γ'.comps.map Local_stripC).map Local_tri := by
      simp [Function.comp_def, Local_tri, Local_stripC]
    rw [e1]
    exact hperm.map _
  -- the dotted and molecular graphs
  have g1 : Γ₀.dotGraph = Δ.dotGraph := by
    unfold Graph.dotGraph
    refine Local_fromRel_congr (fun κ => κ = .dot) fun u v => ⟨?_, ?_⟩
    · rintro ⟨c, hc, hk, hx, hy⟩
      rcases (memΓ₀ c).1 hc with hc | rfl | rfl
      · exact ⟨c, (memΔ c).2 (Or.inl hc), hk, hx, hy⟩
      · rcases hks with h | h <;> rw [h] at hk <;> cases hk
      · simp [mkC] at hk
    · rintro ⟨c, hc, hk, hx, hy⟩
      rcases (memΔ c).1 hc with hc | rfl | rfl
      · exact ⟨c, (memΓ₀ c).2 (Or.inl hc), hk, hx, hy⟩
      · rw [hki] at hk; cases hk
      · rw [hkj] at hk; cases hk
  have g2 : Γ₀.molGraph = (Local_addG Δ (.inr x) (.inr w)).molGraph := by
    unfold Graph.molGraph
    refine Local_fromRel_congr (fun κ => κ.joinsMol = true) fun u v => ⟨?_, ?_⟩
    · rintro ⟨c, hc, hk, hx, hy⟩
      rcases (memΓ₀ c).1 hc with hc | rfl | rfl
      · exact ⟨c, (memD c).2 (Or.inl ((memΔ c).2 (Or.inl hc))), hk, hx, hy⟩
      · rcases hks with h | h <;> rw [h] at hk <;> simp [Kind.joinsMol] at hk
      · exact ⟨_, (memD _).2 (Or.inr rfl), rfl, hx, hy⟩
    · rintro ⟨c, hc, hk, hx, hy⟩
      rcases (memD c).1 hc with hc | rfl
      · rcases (memΔ c).1 hc with hc | rfl | rfl
        · exact ⟨c, (memΓ₀ c).2 (Or.inl hc), hk, hx, hy⟩
        · rw [hki] at hk; simp [Kind.joinsMol] at hk
        · rw [hkj] at hk; simp [Kind.joinsMol] at hk
      · exact ⟨_, (memΓ₀ _).2 (Or.inr (Or.inr rfl)), rfl, hx, hy⟩
  obtain ⟨hρ, hpin, hint⟩ := Local_dotWaved g1 g2
  obtain ⟨hb₀, hfl₀, hu₀⟩ := Local_dot_fun g1
  have hr₀ := Local_mol_fun g2
  have hp : Δ.SameBlock (.inr x) (.inr x) := SimpleGraph.Reachable.refl _
  have hrxw : Local_rho (Local_addG Δ (.inr x) (.inr w)) (.inr x) =
      Local_rho (Local_addG Δ (.inr x) (.inr w)) (.inr w) :=
    (Local_add_rho_q (q := .inr w) hp).symm
  obtain ⟨⟨s₁, C₁, E₁, G₁⟩, P₁⟩ := Local_addDot_main (q := .inr w) hI' (Or.inl ⟨x, hp⟩)
  -- the carrier from the graph with the dotted edge to the term
  have hdot : (Local_rd (Local_addG Δ (.inr x) (.inr w)) (mkC .dot (.inr x) (.inr w))).1 = none := by
    simp [Local_rd, mkC]
  have hwav : (Local_rd (Local_addG Δ (.inr x) (.inr w))
      (mkC (.waved wv) (.inr x) (.inr w))).1 = none := by
    simp [Local_rd, mkC, hrxw]
  have hcar : Local_Carry (Local_addG Δ (.inr x) (.inr w)).toMG' Γ₀.toMG' id := by
    refine Local_carry_trans_id (Local_carry_toRG _) (Local_carry_trans_id ?_
      (Local_carry_trans_id (Local_RG_congr Γ₀.comps hρ hpin hint) (Local_carry_ofRG Γ₀)))
    have hL : (F ++ [solidC ch e'.x e.y] ++ [mkC (.waved wv) (Sum.inr x) (Sum.inr w)]).Perm
        Γ₀.comps := by
      show List.Perm _ (F ++ [_, _])
      simp
    rcases hw with hw | hw
    · refine Local_RG_shape _ (K := F) (D := [e']) (D' := [solidC ch e'.x e.y])
        (R := [e, mkC .dot (.inr x) (.inr w)]) (N := [mkC (.waved wv) (.inr x) (.inr w)])
        ?_ hL ?_ ?_ ?_
      · show List.Perm (Δ.comps ++ [_]) _
        refine (hΔ.append_right _).trans ?_
        perm_tac
      · refine List.Forall₂.cons ?_ List.Forall₂.nil
        unfold Local_SameR
        rw [Local_rd_solidC']
        have : Local_rd (Local_addG Δ (.inr x) (.inr w)) (mkC (.G ch) e'.x e.y) =
            Local_rd (Local_addG Δ (.inr x) (.inr w)) e' := by
          simp only [Local_rd, mkC, hkj, hyj, ← hw, ← hrxw]
        rw [this]
        exact Local_Same.refl _
      · intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · simp [Local_rd, hxi, ← hw, hrxw]
        · exact hdot
      · intro c hc
        rw [List.mem_singleton] at hc
        subst hc
        exact hwav
    · refine Local_RG_shape _ (K := F) (D := [e]) (D' := [solidC ch e'.x e.y])
        (R := [e', mkC .dot (.inr x) (.inr w)]) (N := [mkC (.waved wv) (.inr x) (.inr w)])
        ?_ hL ?_ ?_ ?_
      · show List.Perm (Δ.comps ++ [_]) _
        refine (hΔ.append_right _).trans ?_
        perm_tac
      · refine List.Forall₂.cons ?_ List.Forall₂.nil
        unfold Local_SameR
        rw [Local_rd_solidC']
        have : Local_rd (Local_addG Δ (.inr x) (.inr w)) (mkC (.G ch) e'.x e.y) =
            Local_rd (Local_addG Δ (.inr x) (.inr w)) e := by
          simp only [Local_rd, mkC, hki, hxi, ← hw, ← hrxw]
        rw [this]
        exact Local_Same.refl _
      · intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · simp [Local_rd, hyj, ← hw, hrxw]
        · exact hdot
      · intro c hc
        rw [List.mem_singleton] at hc
        subst hc
        exact hwav
  -- the clauses of `Γ₀`
  have hCC := (Local_colour_iff Δ).1 hC
  have eCC : ∀ c, Local_CC Γ₀ c ↔ Local_CC Δ c := by
    intro c
    simp only [Local_CC, hfl₀]
  have ce := hCC e ((memΔ e).2 (Or.inr (Or.inl rfl)))
  have ce' := hCC e' ((memΔ e').2 (Or.inr (Or.inr rfl)))
  obtain ⟨a1, -⟩ := ce'.1 (by rw [hkj]; rfl)
  obtain ⟨b1, b2, b3, b4⟩ := ce.1 (by rw [hki]; rfl)
  have hC₀ : Γ₀.ColourInvB := by
    refine (Local_colour_iff Γ₀).2 fun c hc => ?_
    rcases (memΓ₀ c).1 hc with hc | rfl | rfl
    · exact (eCC c).2 (hCC c ((memΔ c).2 (Or.inl hc)))
    · rw [eCC]
      unfold solidC
      split_ifs with hab
      · have hne : ∀ a : Fin 3, Δ.flatAtom e'.x ≠ .inl a := by
          intro a h
          rw [h] at a1
          simp at a1
        refine ⟨fun _ => ⟨a1, hne 0, fun h => absurd h (hne 1), fun h => absurd h (hne 2)⟩,
          fun h => by simp [mkC] at h⟩
      · refine ⟨fun _ => ⟨a1, b2, fun h => ?_, fun h => ?_⟩, fun h => by simp [mkC] at h⟩
        · show Kind.G ch = .G .plus
          rw [← hki]
          exact b3 h
        · show Kind.G ch = .G .minus
          rw [← hki]
          exact b4 h
    · exact Local_CC_int rfl rfl
  have hG₀ : Γ₀.NoGhost := by
    intro c hc
    rcases (memΓ₀ c).1 hc with hc | rfl | rfl
    · exact hG c ((memΔ c).2 (Or.inl hc))
    · rcases hks with h | h <;> rw [h] <;> simp
    · simp [mkC]
  have hdc : ∀ c, c.kind.isDiffusive = true → (c ∈ Γ₀.comps ↔ c ∈ Δ.comps) := by
    intro c hd
    constructor
    · intro hc
      rcases (memΓ₀ c).1 hc with hc | rfl | rfl
      · exact (memΔ c).2 (Or.inl hc)
      · rcases hks with h | h <;> rw [h] at hd <;> simp [Kind.isDiffusive] at hd
      · simp [mkC, Kind.isDiffusive] at hd
    · intro hc
      rcases (memΔ c).1 hc with hc | rfl | rfl
      · exact (memΓ₀ c).2 (Or.inl hc)
      · rw [hki] at hd; simp [Kind.isDiffusive] at hd
      · rw [hkj] at hd; simp [Kind.isDiffusive] at hd
  have hdiff : ∀ u, Γ₀.DiffToPinned u ↔ Δ.DiffToPinned u := by
    intro u
    unfold Graph.DiffToPinned
    rw [hu₀]
    exact ⟨fun h c hc hd => h c ((hdc c hd).2 hc) hd, fun h c hc hd => h c ((hdc c hd).1 hc) hd⟩
  have hhas : ∀ u, Γ₀.HasDiffToPinned u ↔ Δ.HasDiffToPinned u := by
    intro u
    unfold Graph.HasDiffToPinned
    rw [hu₀]
    exact ⟨fun ⟨c, hc, hd, h⟩ => ⟨c, (hdc c hd).1 hc, hd, h⟩,
      fun ⟨c, hc, hd, h⟩ => ⟨c, (hdc c hd).2 hc, hd, h⟩⟩
  have hdeg : ∀ u : Atom 3 n, u.isLeft = true → Γ₀.nonDotDeg u ≤ Δ.nonDotDeg u := by
    intro u hu
    unfold Graph.nonDotDeg
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter, hΔ.countP_eq]
    refine Local_countP_le2 _ F _ _ _ _ ?_ ?_
    · exact decide_eq_false (by
        rintro ⟨h | h, -⟩ <;> simp only [mkC] at h <;> subst h <;> simp at hu)
    · simp only [decide_eq_true_eq, hsx, hsy, hki, hkj]
      rintro ⟨h | h, -⟩
      · right
        exact ⟨Or.inl h, by simp, by simp⟩
      · left
        exact ⟨Or.inr h, by simp, by simp⟩
  have hE₀ : Γ₀.ExtClause := by
    obtain ⟨x1, x2, x3, x4, x5⟩ := hE
    unfold Graph.ExtClause
    rw [hb₀, hu₀]
    refine ⟨x1, fun c hc hk => ?_, fun h => ⟨(hhas _).2 (x3 h).1, (hdiff _).2 (x3 h).2⟩,
      fun h => ⟨fun c hc hd => (x4 h).1 c ((hdc c hd).1 hc) hd, (hdeg _ rfl).trans (x4 h).2⟩,
      fun h => ⟨?_, (hdiff _).2 (x5 h).2.1, (hdeg _ rfl).trans (x5 h).2.2⟩⟩
    · rcases (memΓ₀ c).1 hc with hc | rfl | rfl
      · exact x2 c ((memΔ c).2 (Or.inl hc)) hk
      · rcases hks with h | h <;> rw [h] at hk <;> cases hk
      · simp [mkC] at hk
    · have hf1 : Δ.flatAtom (.inl 1) = .inl 1 := Local_flat_unpinned h
      rcases (x5 h).1 with ⟨c, hc, hk, hat⟩ | hd
      · rcases (memΔ c).1 hc with hc | rfl | rfl
        · exact Or.inl ⟨c, (memΓ₀ c).2 (Or.inl hc), hk, hat⟩
        · have hey : c.y = .inl 1 := hat.resolve_left (by rw [hxi]; simp)
          have hch : ch = .plus := by
            rw [hki] at hk
            cases hk
            rfl
          have hne : e'.x ≠ c.y := by
            intro heq
            rw [heq, hey, hf1] at a1
            simp at a1
          refine Or.inl ⟨solidC ch e'.x c.y, (memΓ₀ _).2 (Or.inr (Or.inl rfl)), ?_, Or.inr (hsy.trans hey)⟩
          unfold solidC
          simp only [hne, if_false, hch]
          rfl
        · have hex : c.x = .inl 1 := hat.resolve_right (by rw [hyj]; simp)
          rw [hex, hf1] at a1
          simp at a1
      · exact Or.inr ((hhas _).2 hd)
  -- assembling
  obtain ⟨sp₀, ng₀, dj₀, pl₀⟩ := hcar (Graph.toMG'_disjoint _) (Graph.toMG'_noGhost _ G₁) s₁
  obtain ⟨sp', -, -, pl'⟩ := Local_same3_carry hS dj₀ ng₀ sp₀
  have cl := Local_same3_clauses hS
  have hr' : Γ'.molRep = Γ₀.molRep := (Local_same3_fun hS).2.2.2.1
  have hwx : (Local_addG Δ (.inr x) (.inr w)).molRep (.inr w) =
      (Local_addG Δ (.inr x) (.inr w)).molRep (.inr x) :=
    (Local_molRep_eq_iff _ _ _).2 (Or.inr ⟨rfl, rfl,
      SimpleGraph.Reachable.mono (Local_dot_le_mol _) (Local_add_sameBlock_pq).symm⟩)
  refine ⟨⟨sp', cl.1.2 hC₀, cl.2.1.2 hE₀, cl.2.2.2 hG₀⟩, rfl,
    (Local_addG Δ (.inr x) (.inr w)).molRep, Local_pull_trans P₁ (Local_pull_trans pl₀ pl'), ?_,
    fun _ c hc pq u hl => ?_⟩
  · rw [Local_add_molRep_molRep, hr', hr₀]
    rfl
  · rw [hlab c hc pq u hl, hr', hr₀, hwx]
    rfl

/-! ### Complex conjugation and the transposition of the solid edges -/

private theorem Local_eraseIdxs_map {α β : Type*} (S : List ℕ) (l : List α) (f : α → β) :
    eraseIdxs S (l.map f) = (eraseIdxs S l).map f := by
  simp [eraseIdxs, List.zipIdx_map, List.filter_map, Function.comp_def]

private theorem Local_eraseIdxs_comm {α : Type*} (i j : ℕ) (l : List α) :
    eraseIdxs [j, i] l = eraseIdxs [i, j] l := by
  unfold eraseIdxs
  congr 2
  funext p
  simp [Bool.or_comm]

private theorem Local_getElem_map {α β : Type*} {l : List α} {l' : List β} {f : α → β}
    (h : l' = l.map f) {i : ℕ} (hi : i < l.length) :
    ∃ hi' : i < l'.length, l'[i] = f l[i] := by
  subst h
  exact ⟨by simpa using hi, by simp⟩

/-- `Local_GM` under complex conjugation. -/
private theorem Local_GM_conj {Δ Δc : Graph 3 n} {x : Fin n} {t : Tracked 3 n}
    (h : Δc.comps = Δ.comps.map Local_conjC) (hg : Local_GM Δ x t) :
    Local_GM Δc x ⟨t.nOut, t.g.conj, t.f⟩ := by
  obtain ⟨Γ', rfl, i, j, hi, hj, ch, w, wv, hij, hki, hkj, hxi, hyj, hw, hperm, hlab⟩ := hg
  obtain ⟨hi', ei⟩ := Local_getElem_map h hi
  obtain ⟨hj', ej⟩ := Local_getElem_map h hj
  obtain ⟨wv', hwv'⟩ : ∃ wv', (Kind.waved wv).conj = .waved wv' := by
    cases wv <;> exact ⟨_, rfl⟩
  refine ⟨Γ'.conj, rfl, i, j, hi', hj', ch.flip, w, wv', hij, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ei]
    simp [Local_conjC, hki, Kind.conj]
  · rw [ej]
    simp [Local_conjC, hkj, Kind.conj]
  · rw [ei]
    exact hxi
  · rw [ej]
    exact hyj
  · rw [ei, ej]
    exact hw
  · rw [ei, ej, h, Local_eraseIdxs_map]
    have := hperm.map Local_conjC
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil,
      Local_conjC_solidC] at this
    have e1 : Local_conjC (mkC (.waved wv) (Sum.inr x : Atom 3 n) (.inr w)) =
        mkC (.waved wv') (.inr x) (.inr w) := by
      simp [Local_conjC, mkC, hwv']
    rw [e1] at this
    simp only [Graph.conj, List.map_map, List.map_append, List.map_cons, List.map_nil]
    convert this using 2 <;> first | rfl | (funext c; rfl) |
      simp [List.map_map, Function.comp_def, Local_conjC, Local_stripC]
  · intro c hc pq u hl
    simp only [Graph.conj, List.mem_map] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    exact hlab c₀ hc₀ pq u hl

private theorem Local_sw_kind {V : Type} (c : Comp V) : c.swapSolid.kind = c.kind := by
  unfold Comp.swapSolid
  split <;> rfl

private theorem Local_sw_label {V : Type} (c : Comp V) : c.swapSolid.label = c.label := by
  unfold Comp.swapSolid
  split <;> rfl

private theorem Local_sw_of_not {V : Type} {c : Comp V} (h : c.kind.isSolid = false) :
    c.swapSolid = c := by
  simp [Comp.swapSolid, h]

private theorem Local_sw_of_solid {V : Type} {c : Comp V} (h : c.kind.isSolid = true) :
    c.swapSolid = { c with x := c.y, y := c.x } := by
  simp [Comp.swapSolid, h]

private theorem Local_sw_sw {V : Type} (c : Comp V) : c.swapSolid.swapSolid = c := by
  cases hs : c.kind.isSolid
  · rw [Local_sw_of_not hs, Local_sw_of_not hs]
  · rw [Local_sw_of_solid hs, Local_sw_of_solid (by simpa using hs)]

private theorem Local_sw_strip {V : Type} (c : Comp V) :
    Local_stripC c.swapSolid = (Local_stripC c).swapSolid := by
  cases hs : c.kind.isSolid
  · rw [Local_sw_of_not hs, Local_sw_of_not (c := Local_stripC c) hs]
  · rw [Local_sw_of_solid hs, Local_sw_of_solid (c := Local_stripC c) hs]
    rfl

private theorem Local_sw_map {V W : Type} (f : V → W) (c : Comp V) :
    c.swapSolid.map f = (c.map f).swapSolid := by
  cases hs : c.kind.isSolid
  · rw [Local_sw_of_not hs, Local_sw_of_not (c := c.map f) hs]
  · rw [Local_sw_of_solid hs, Local_sw_of_solid (c := c.map f) hs]
    rfl

private theorem Local_sw_solidC {V : Type} [DecidableEq V] (ch : Charge) (a b : V) :
    (solidC ch a b).swapSolid = solidC ch b a := by
  unfold solidC
  by_cases h : a = b
  · subst h
    simp only [if_true]
    exact Local_sw_of_not rfl
  · rw [if_neg h, if_neg (Ne.symm h), Local_sw_of_solid rfl]
    rfl

private theorem Local_sw_mkC_waved {V : Type} (wv : Wave) (a b : V) :
    (mkC (.waved wv) a b).swapSolid = mkC (.waved wv) a b :=
  Local_sw_of_not rfl

private theorem Local_sw_graphs {k : ℕ} {Δ Δs : Graph k n}
    (h : Δs.comps = Δ.comps.map Comp.swapSolid) :
    Δs.dotGraph = Δ.dotGraph ∧ Δs.molGraph = Δ.molGraph := by
  have key : ∀ (P : Kind → Prop), (∀ ch, ¬ P (.G ch)) → ∀ u v,
      (∃ c ∈ Δs.comps, P c.kind ∧ c.x = u ∧ c.y = v) ↔
        (∃ c ∈ Δ.comps, P c.kind ∧ c.x = u ∧ c.y = v) := by
    intro P hP u v
    have hns : ∀ c : Comp (Atom k n), P c.kind → c.swapSolid = c := by
      intro c hc
      refine Local_sw_of_not ?_
      cases hk : c.kind <;> simp_all [Kind.isSolid]
    rw [h]
    constructor
    · rintro ⟨c', hc', hp, hx, hy⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
      rw [Local_sw_kind] at hp
      rw [hns c hp] at hx hy
      exact ⟨c, hc, hp, hx, hy⟩
    · rintro ⟨c, hc, hp, hx, hy⟩
      exact ⟨c.swapSolid, List.mem_map_of_mem hc, by rw [Local_sw_kind]; exact hp,
        by rw [hns c hp]; exact hx, by rw [hns c hp]; exact hy⟩
  constructor
  · ext u v
    simp only [Graph.dotGraph, SimpleGraph.fromRel_adj]
    rw [key (fun κ => κ = .dot) (fun _ h => by cases h) u v,
      key (fun κ => κ = .dot) (fun _ h => by cases h) v u]
  · ext u v
    simp only [Graph.molGraph, SimpleGraph.fromRel_adj]
    rw [key (fun κ => κ.joinsMol = true) (fun _ h => by simp [Kind.joinsMol] at h) u v,
      key (fun κ => κ.joinsMol = true) (fun _ h => by simp [Kind.joinsMol] at h) v u]

private theorem Local_sw_rd {k : ℕ} {Δ Δs : Graph k n} (h : Δs.comps = Δ.comps.map Comp.swapSolid)
    (c : Comp (Atom k n)) :
    Local_rd Δs c.swapSolid = if c.kind.isSolid then ((Local_rd Δ c).1, (Local_rd Δ c).2.swap)
      else Local_rd Δ c := by
  obtain ⟨hd, hm⟩ := Local_sw_graphs h
  have hρ := (Local_graphs_rho hd hm).1
  cases hs : c.kind.isSolid
  · rw [Local_sw_of_not hs]
    simp only [Local_rd, hρ, Bool.false_eq_true, ↓reduceIte]
  · rw [Local_sw_of_solid hs]
    simp only [Local_rd, hρ, if_true, Prod.swap, eq_comm (a := Local_rho Δ c.y)]

private theorem Local_sw_same {V : Type} {e e' : Local_Ed V} (h : Local_Same e e') :
    Local_Same (e.1, e.2.swap) (e'.1, e'.2.swap) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, Or.inl (by simp [h2])⟩
  · exact Or.inr ⟨h1, Or.inr (by simp [h2])⟩

/-- `Local_Dec` under the transposition of the solid edges. -/
private theorem Local_dec_sw {Δ Δs : Graph 3 n} {x : Fin n} {j : ℕ} {Δ' Δ's : Graph 3 (n + j)}
    (h : Δs.comps = Δ.comps.map Comp.swapSolid) (h' : Δ's.comps = Δ'.comps.map Comp.swapSolid)
    (hd : Local_Dec Δ x j Δ') : Local_Dec Δs x j Δ's := by
  obtain ⟨K, D, P, R, D', P', N, h1, h2, h3, h4, h5, h6, h7⟩ := hd
  have hfun := Local_graphs_fun (Local_sw_graphs h).1 (Local_sw_graphs h).2
  have hst : ∀ l : List (Comp (Atom 3 n)),
      (l.map Comp.swapSolid).map Local_stripC = (l.map Local_stripC).map Comp.swapSolid := by
    intro l
    simp only [List.map_map]
    exact List.map_congr_left fun c _ => Local_sw_strip c
  have hst' : ∀ l : List (Comp (Atom 3 (n + j))),
      (l.map Comp.swapSolid).map Local_stripC = (l.map Local_stripC).map Comp.swapSolid := by
    intro l
    simp only [List.map_map]
    exact List.map_congr_left fun c _ => Local_sw_strip c
  have hlift : liftCs j (K.map Comp.swapSolid) = (liftCs j K).map Comp.swapSolid := by
    simp only [liftCs, List.map_map]
    exact List.map_congr_left fun c _ => Local_sw_map _ c
  refine ⟨K.map Comp.swapSolid, D.map Comp.swapSolid, P.map Comp.swapSolid,
    R.map Comp.swapSolid, D'.map Comp.swapSolid, P'.map Comp.swapSolid, N.map Comp.swapSolid,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h, hst]
    have := h1.map Comp.swapSolid
    simp only [List.map_append] at this
    exact this
  · rw [h', hst', hlift]
    have := h2.map Comp.swapSolid
    simp only [List.map_append] at this
    exact this
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine h3.imp fun d d' hm => ?_
    obtain ⟨hkd, hr, hx, hy, hs⟩ := hm
    have hsol : d'.kind.isSolid = d.kind.isSolid := by
      rcases hkd with hkd | ⟨w1, w2⟩
      · rw [hkd]
      · have a : ∀ κ : Kind, κ.isWeight = true → κ.isSolid = false := by
          intro κ hκ
          cases κ <;> simp_all [Kind.isWeight, Kind.isSolid]
        rw [a _ w1, a _ w2]
    refine ⟨by simp only [Local_sw_kind]; exact hkd, by rw [Local_sw_kind]; exact hr, ?_, ?_, ?_⟩
    · cases hds : d.kind.isSolid
      · rw [Local_sw_of_not hds, Local_sw_of_not (hsol.trans hds)]
        exact hx
      · rw [Local_sw_of_solid hds, Local_sw_of_solid (hsol.trans hds)]
        exact hy
    · cases hds : d.kind.isSolid
      · rw [Local_sw_of_not hds, Local_sw_of_not (hsol.trans hds)]
        exact hy
      · rw [Local_sw_of_solid hds, Local_sw_of_solid (hsol.trans hds)]
        exact hx
    · unfold Local_SameR at hs ⊢
      rw [Local_sw_map, Local_sw_rd h, Local_sw_rd h]
      have hk' : (d'.map (Local_proj j x)).kind = d'.kind := rfl
      rw [hk', hsol]
      split_ifs
      · exact Local_sw_same hs
      · exact hs
  · rcases h4 with ⟨rfl, rfl⟩ | ⟨c, ch, u, v, rfl, hkc, hu, hv, hxu, hxv, hp⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · right
      have hpm := hp.map Comp.swapSolid
      simp only [List.map_cons, List.map_nil, Local_sw_solidC] at hpm
      rcases hkc with hkc | hkc | hkc
      · refine ⟨c.swapSolid, ch, v, u, rfl, Or.inl (by rw [Local_sw_kind]; exact hkc), hv, hu,
          by rw [hfun.2.1]; exact hxv, by rw [hfun.2.1]; exact hxu, ?_⟩
        have hs : c.kind.isSolid = true := by rw [hkc]; rfl
        have hw : c.kind.isWeight = false := by rw [hkc]; rfl
        rw [Local_sw_of_solid hs]
        simp only [hw] at hpm
        simp only [hw, Bool.false_eq_true, if_false]
        exact hpm.trans (List.Perm.swap _ _ _)
      · refine ⟨c.swapSolid, ch, v, u, rfl, Or.inr (Or.inl (by rw [Local_sw_kind]; exact hkc)), hv,
          hu, by rw [hfun.2.1]; exact hxv, by rw [hfun.2.1]; exact hxu, ?_⟩
        have hs : c.kind.isSolid = false := by rw [hkc]; rfl
        have hw : c.kind.isWeight = true := by rw [hkc]; rfl
        rw [Local_sw_of_not hs]
        simp only [hw, if_true] at hpm ⊢
        exact hpm.trans (List.Perm.swap _ _ _)
      · refine ⟨c.swapSolid, ch, v, u, rfl, Or.inr (Or.inr (by rw [Local_sw_kind]; exact hkc)), hv,
          hu, by rw [hfun.2.1]; exact hxv, by rw [hfun.2.1]; exact hxu, ?_⟩
        have hs : c.kind.isSolid = false := by rw [hkc]; rfl
        have hw : c.kind.isWeight = true := by rw [hkc]; rfl
        rw [Local_sw_of_not hs]
        simp only [hw, if_true] at hpm ⊢
        exact hpm.trans (List.Perm.swap _ _ _)
  · intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    rw [Local_sw_kind]
    exact h5 c₀ hc₀
  · intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h6 c₀ hc₀
    have hk := Local_sw_kind c₀
    cases hs : c₀.kind.isSolid
    · rw [Local_sw_of_not hs]
      refine ⟨a1, a2, a3, a4, a5, a6, ?_, fun e => ?_⟩
      · rw [show c₀.map (Local_proj j x) = (c₀.map (Local_proj j x)).swapSolid from
          (Local_sw_of_not (c := c₀.map (Local_proj j x)) hs).symm, Local_sw_rd h]
        simp only [Comp.map, hs, Bool.false_eq_true, if_false]
        exact a7
      · rw [hfun.2.1]
        exact a8 e
    · have hj : c₀.kind.joinsMol = false := (Local_solid_kinds hs).2.2.2
      rw [Local_sw_of_solid hs]
      refine ⟨a2, a1, a3, a4, a5, a6, ?_, fun e => absurd e (by rw [hj]; simp)⟩
      have := Local_sw_rd h (c₀.map (Local_proj j x))
      rw [Local_sw_of_solid (c := c₀.map (Local_proj j x)) hs] at this
      simp only [Comp.map, hs, if_true] at this ⊢
      rw [this]
      exact a7
  · intro i
    rw [(Local_sw_graphs h').2]
    exact h7 i

/-- `Local_DecT` under the transposition of the solid edges. -/
private theorem Local_decT_sw {Δ Δs : Graph 3 n} {x : Fin n} {t : Tracked 3 n}
    (h : Δs.comps = Δ.comps.map Comp.swapSolid) (hd : Local_DecT Δ x t) :
    Local_DecT Δs x ⟨t.nOut, t.g.swapSolid, t.f⟩ := by
  obtain ⟨j, hn, hf, hdec, hl⟩ := hd
  obtain ⟨tn, tg, tf⟩ := t
  simp only at hn
  subst hn
  refine ⟨j, rfl, hf, Local_dec_sw h rfl hdec, fun c hc pq u hlu => ?_⟩
  simp only [Graph.swapSolid] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  rw [(Local_graphs_fun (Local_sw_graphs h).1 (Local_sw_graphs h).2).2.1]
  rw [Local_sw_label] at hlu
  exact hl c₀ hc₀ pq u hlu

/-- `Local_GM` under the transposition of the solid edges: the two solid edges at `x` exchange
their roles. -/
private theorem Local_GM_sw {Δ Δs : Graph 3 n} {x : Fin n} {t : Tracked 3 n}
    (h : Δs.comps = Δ.comps.map Comp.swapSolid) (hg : Local_GM Δ x t) :
    Local_GM Δs x ⟨t.nOut, t.g.swapSolid, t.f⟩ := by
  obtain ⟨Γ', rfl, i, j, hi, hj, ch, w, wv, hij, hki, hkj, hxi, hyj, hw, hperm, hlab⟩ := hg
  obtain ⟨hi', ei⟩ := Local_getElem_map h hi
  obtain ⟨hj', ej⟩ := Local_getElem_map h hj
  have hsi : Δ.comps[i].kind.isSolid = true := by rw [hki]; rfl
  have hsj : Δ.comps[j].kind.isSolid = true := by rw [hkj]; rfl
  refine ⟨Γ'.swapSolid, rfl, j, i, hj', hi', ch, w, wv, Ne.symm hij, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ej, Local_sw_kind]
    exact hkj
  · rw [ei, Local_sw_kind]
    exact hki
  · rw [ej, Local_sw_of_solid hsj]
    exact hyj
  · rw [ei, Local_sw_of_solid hsi]
    exact hxi
  · rw [ei, ej, Local_sw_of_solid hsi, Local_sw_of_solid hsj]
    exact hw.symm
  · rw [ei, ej, Local_sw_of_solid hsi, Local_sw_of_solid hsj, h, Local_eraseIdxs_map,
      Local_eraseIdxs_comm]
    have := hperm.map Comp.swapSolid
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, Local_sw_solidC,
      Local_sw_mkC_waved] at this
    simp only [Graph.swapSolid, List.map_map, List.map_append, List.map_cons, List.map_nil]
    have e1 : (Local_stripC ∘ Comp.swapSolid : Comp (Atom 3 n) → Comp (Atom 3 n)) =
        Comp.swapSolid ∘ Local_stripC := by
      funext c
      exact Local_sw_strip c
    rw [e1]
    convert this using 2
  · intro c hc pq u hl
    simp only [Graph.swapSolid, List.mem_map] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    rw [Local_sw_label] at hl
    exact hlab c₀ hc₀ pq u hl

/-! ### The `GG` expansion and its transposed form -/

private theorem Local_kind_conj_isSolid (κ : Kind) : κ.conj.isSolid = κ.isSolid := by
  cases κ with
  | G c => cases c <;> rfl
  | weight c => cases c <;> rfl
  | light c => cases c <;> rfl
  | inv c => cases c <;> rfl
  | wD c d => cases c <;> rfl
  | waved w => cases w <;> rfl
  | _ => rfl

private theorem Local_conj_out {Γ : Graph 3 n} {x : Fin n} (h : Γ.GGOutInt (.inr x)) :
    Γ.conj.GGOutInt (.inr x) := by
  intro c hc hs hx
  simp only [Graph.conj, List.mem_map] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  exact h c₀ hc₀ (by rw [← Local_kind_conj_isSolid]; exact hs) hx

private theorem Local_sw_out {Γ : Graph 3 n} {x : Fin n} (h : Γ.GGInInt (.inr x)) :
    Γ.swapSolid.GGOutInt (.inr x) := by
  intro c hc hs hx
  simp only [Graph.swapSolid, List.mem_map] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  rw [Local_sw_kind] at hs
  rw [Local_sw_of_solid hs] at hx ⊢
  exact h c₀ hc₀ hs hx

private theorem Local_sw_labelFree {Γ : Graph 3 n} (h : Γ.LabelFree) : Γ.swapSolid.LabelFree := by
  intro c hc
  simp only [Graph.swapSolid, List.mem_map] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  rw [Local_sw_label]
  exact h c₀ hc₀

private theorem Local_sw_sw_comps (Γ : Graph 3 n) :
    Γ.comps = Γ.swapSolid.comps.map Comp.swapSolid := by
  simp only [Graph.swapSolid, List.map_map]
  conv_lhs => rw [← List.map_id Γ.comps]
  exact List.map_congr_left fun c _ => (Local_sw_sw c).symm

private theorem Local_res_good {Δ : Graph 3 n} (hI : Local_Inv Δ) (hlf : Δ.LabelFree) {x : Fin n}
    {t : Tracked 3 n} (h : Local_DecT Δ x t ∨ Local_GM Δ x t) : Local_Good Δ (.inr x) t :=
  h.elim (Local_good_of_decT hI) (Local_good_of_GM hI hlf)

private theorem Local_dot_after {Γ : Graph 3 n} {x : Fin n} {E : TExpansion 3 n}
    (hE : ∀ t ∈ E, Local_Good Γ (.inr x) t) :
    ∀ t ∈ E.bind (fun _ g => oDotT g), Local_Good Γ (.inr x) t := by
  refine Local_good_bind hE fun t ht s hs => ?_
  obtain ⟨hI', hx', -⟩ := hE t ht
  exact Local_oDot_good hI' _ hx' s hs

/-- **[II, Lemma 5.10] for `O_GG`** at an internal atom whose outgoing solid edges end at internal
atoms, on a graph without labels with the invariant. -/
private theorem Local_oGG_good {Γ : Graph 3 n} (hI : Local_Inv Γ) (hlf : Γ.LabelFree) (x : Fin n)
    (hout : Γ.GGOutInt (.inr x)) : ∀ t ∈ oGGT (.inr x) Γ, Local_Good Γ (.inr x) t := by
  intro t ht
  unfold oGGT at ht
  split_ifs at ht with hp
  · rw [List.mem_singleton] at ht
    subst ht
    exact Local_good_self hI _ rfl
  split at ht
  · rename_i E hE
    exact Local_dot_after (fun t ht => Local_res_good hI hlf (Local_ggPos_res hlf x hout hE t ht))
      t ht
  · split at ht
    · rename_i E _ hE
      refine Local_dot_after (fun t ht => ?_) t ht
      unfold TExpansion.conj at ht
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
      have hc := Local_conj_conj_comps Γ
      rcases Local_ggPos_res (Local_conj_labelFree hlf) x (Local_conj_out hout) hE t₀ ht₀ with
        h | h
      · exact Local_good_of_decT hI (Local_decT_conj hc h)
      · exact Local_good_of_GM hI hlf (Local_GM_conj hc h)
    · rw [List.mem_singleton] at ht
      subst ht
      exact Local_good_self hI _ rfl

/-- **[II, Lemma 5.10] for the transposed `O_GG`** at an internal atom whose incoming solid edges
start at internal atoms, on a graph without labels with the invariant. -/
private theorem Local_oGGT_good {Γ : Graph 3 n} (hI : Local_Inv Γ) (hlf : Γ.LabelFree) (x : Fin n)
    (hin : Γ.GGInInt (.inr x)) : ∀ t ∈ oGGTT (.inr x) Γ, Local_Good Γ (.inr x) t := by
  intro t ht
  unfold oGGTT at ht
  split_ifs at ht with hp
  · rw [List.mem_singleton] at ht
    subst ht
    exact Local_good_self hI _ rfl
  have hs := Local_sw_sw_comps Γ
  have hlfs := Local_sw_labelFree hlf
  have houts := Local_sw_out hin
  split at ht
  · rename_i E hE
    refine Local_dot_after (fun t ht => ?_) t ht
    unfold TExpansion.swapSolid at ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
    rcases Local_ggPos_res hlfs x houts hE t₀ ht₀ with h | h
    · exact Local_good_of_decT hI (Local_decT_sw hs h)
    · exact Local_good_of_GM hI hlf (Local_GM_sw hs h)
  · split at ht
    · rename_i E _ hE
      refine Local_dot_after (fun t ht => ?_) t ht
      unfold TExpansion.swapSolid TExpansion.conj at ht
      rw [List.map_map] at ht
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht
      have hc := Local_conj_conj_comps Γ.swapSolid
      rcases Local_ggPos_res (Local_conj_labelFree hlfs) x (Local_conj_out houts) hE t₀ ht₀ with
        h | h
      · exact Local_good_of_decT hI (Local_decT_sw hs (Local_decT_conj hc h))
      · exact Local_good_of_GM hI hlf (Local_GM_sw hs (Local_GM_conj hc h))
    · rw [List.mem_singleton] at ht
      subst ht
      exact Local_good_self hI _ rfl

/-- **[II, Lemma 5.10] for the local expansions** at an internal atom of a graph without labels
with the invariant, with the `GG` expansion in the form of `Graph.LocSide`. -/
private theorem Local_localOp_good {Γ : Graph 3 n} (hI : Local_Inv Γ) (hlf : Γ.LabelFree)
    (x : Fin n) (o : Fin 5) (hs : Γ.LocSide o (.inr x)) :
    ∀ t ∈ localOp' o (.inr x) Γ, Local_Good Γ (.inr x) t := by
  obtain ⟨hs2, hs4⟩ := hs
  match o with
  | 0 => exact Local_oWeight_good hI hlf x
  | 1 => exact Local_oMultiE_good hI hlf x
  | 2 => exact Local_oGG_good hI hlf x (hs2 rfl rfl)
  | 3 => exact Local_oGGbar_good hI hlf x
  | 4 => exact Local_oGGT_good hI hlf x (hs4 rfl rfl)

end OGG

/-! ## [II, Lemma 5.10] and [II, Lemma 6.4] in the block reading -/

/-- **[II, Lemma 5.10]** (atomic form) in the block reading: on graphs with the clause on the
external atoms, the charge pattern of the block normal form and no ghost edge, `O_dot` on a
regular graph and the local expansions at an internal atom on a normal regular graph without
labels, with the `GG` expansion in the form of `Graph.LocSide`, keep `spdPM'` and the clause on
the external atoms. -/
theorem localSPDB :
  ∀ (n₀ C : ℕ) (x : Fin n₀) (Γ : Graph 3 n₀), spdPM' Γ → Γ.ExtClause → Γ.NoGhost →
    Γ.ColourInvB →
    (Γ.Regular C → ∀ t ∈ oDotT Γ, spdPM' t.g ∧ t.g.ExtClause) ∧
    (Γ.Normal C → Γ.LabelFree → Γ.Plain → ∀ o : Fin 5, Γ.LocSide o (.inr x) →
      ∀ t ∈ localOp' o (.inr x) Γ, spdPM' t.g ∧ t.g.ExtClause) := by
  intro n₀ C x Γ hs hE hG hC
  have hI : Local_Inv Γ := ⟨hs, hC, hE, hG⟩
  refine ⟨fun _ t ht => ?_, fun _ hlf _ o ho t ht => ?_⟩
  · obtain ⟨⟨h1, -, h3, -⟩, -⟩ := Local_oDot_good hI (.inr x) rfl t ht
    exact ⟨h1, h3⟩
  · obtain ⟨⟨h1, -, h3, -⟩, -⟩ := Local_localOp_good hI hlf x o ho t ht
    exact ⟨h1, h3⟩

/-- **[II, Lemma 6.4 (1)]** in the block reading: the statement of `localSPDB` for the globally
standard property `gsPM'`. -/
theorem localGSB :
  ∀ (n₀ C : ℕ) (x : Fin n₀) (Γ : Graph 3 n₀), gsPM' Γ → Γ.ExtClause → Γ.NoGhost →
    Γ.ColourInvB →
    (Γ.Regular C → ∀ t ∈ oDotT Γ, gsPM' t.g ∧ t.g.ExtClause) ∧
    (Γ.Normal C → Γ.LabelFree → Γ.Plain → ∀ o : Fin 5, Γ.LocSide o (.inr x) →
      ∀ t ∈ localOp' o (.inr x) Γ, gsPM' t.g ∧ t.g.ExtClause) := by
  intro n₀ C x Γ hs hE hG hC
  have hI : Local_Inv Γ := ⟨hs.1, hC, hE, hG⟩
  have key : ∀ t, Local_Good Γ (.inr x) t → gsPM' t.g ∧ t.g.ExtClause := by
    rintro t ⟨⟨h1, -, h3, -⟩, -, φ, hp, -⟩
    exact ⟨Local_pull_gs hp hs h1, h3⟩
  exact ⟨fun _ t ht => key t (Local_oDot_good hI (.inr x) rfl t ht),
    fun _ hlf _ o ho t ht => key t (Local_localOp_good hI hlf x o ho t ht)⟩

/-- **[II, Lemma 6.4 (2)]** in the block reading: a local expansion at an internal atom of the
minimal isolated subset of `Graph.toMG'` of a globally standard graph (`gsPM'`) with the clause
on the external atoms, the charge pattern of the block normal form and no ghost edge, with the
`GG` expansion in the form of `Graph.LocSide`, gives `Q`-graphs with `Graph.QLabelInMISB`. -/
theorem localQLabelB :
  ∀ (n₀ C : ℕ) (x : Fin n₀) (Γ : Graph 3 n₀), Γ.Normal C → Γ.LabelFree → Γ.Plain → gsPM' Γ →
    Γ.ExtClause → Γ.NoGhost → Γ.ColourInvB → Γ.molRep (.inr x) ∈ Γ.toMG'.MIS →
    ∀ o : Fin 5, Γ.LocSide o (.inr x) → ∀ t ∈ localOp' o (.inr x) Γ, t.g.IsQGraph →
      t.g.QLabelInMISB := by
  intro n₀ C x Γ _ hlf _ hs hE hG hC hmis o ho t ht _ c hc u hl
  obtain ⟨-, -, φ, hp, hφ, hlab⟩ := Local_localOp_good ⟨hs.1, hC, hE, hG⟩ hlf x o ho t ht
  have hL : Local_LabAt Γ (Γ.molRep (.inr x)) := fun c hc pq u hl => by
    rw [hlf c hc] at hl
    cases hl
  left
  rw [hlab hL c hc .Q u hl, ← hφ]
  exact Local_pull_MIS hp hmis

section Instances

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

/-! ### Decidability on atomic graphs -/

/-- The kind is not a `(G_{xx})⁻¹` weight. -/
private def Local_notInvB : Kind → Bool
  | .inv _ => false
  | _ => true

/-- The kind is not a `W_D` weight. -/
private def Local_notWDB : Kind → Bool
  | .wD _ _ => false
  | _ => true

private theorem Local_notInvB_iff (κ : Kind) : (∀ ch, κ ≠ .inv ch) ↔ Local_notInvB κ = true := by
  cases κ <;> simp [Local_notInvB]

private theorem Local_notWDB_iff (κ : Kind) : (∀ ch d, κ ≠ .wD ch d) ↔ Local_notWDB κ = true := by
  cases κ <;> simp [Local_notWDB]

private instance Local_decPlain {k n : ℕ} (Γ : Graph k n) : Decidable Γ.Plain :=
  decidable_of_iff (∀ c ∈ Γ.comps, c.minor = [] ∧ Local_notInvB c.kind = true ∧
    Local_notWDB c.kind = true ∧ (c.kind = .dot → c.x ≠ c.y) ∧
    ((c.kind.isWeight = true → c.y = c.x) ∧ (c.label.isSome = true → c.kind.isRandom = true)))
    (by simp only [Graph.Plain, Comp.WF, Local_notInvB_iff, Local_notWDB_iff])

section Helpers

variable {V E : Type}

end Helpers

end Instances

end RBM8D.Graphs
