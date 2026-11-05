import RBM8D.TExp.Closure
import RBM8D.Bound.GraphAbs
import RBM8D.TExp.Second
import RBM8D.LocalLaw.Primed

/-!
# The self-energy step [II, Lemma 3.9] = [I, Lemma 5.8]: parity, odd orders, the bound step

* The scaling order of a deterministic graph is even ([I, (2.17)], [II, (2.6)]); the shape of an
  `l`-th order self-energy at odd `l` forces the empty formal sum, and `selfEnergyStepStmt`
  holds at odd orders for every variance family (`G13.selfEnergyStep_odd`).
* `G13.boundStepStmt`: [I, (1.26)-(1.27)] for `Σ_n`, `n ≥ 4` even, for the family `smatVar P`;
  it gives `selfEnergyStepStmt d (smatVar P)` (`G13.selfEnergyStep_of_boundStep`).
* The sizes of [I, (5.39)] at order `n` (`G13.window`), the exponents `c₀'`, `c₁'` with
  `window ⊆ adm(c₀', c₁')`, the filter `G13.windowFilter` along them, its monotonicity to
  `llFilter d (n - 1) c₀' c₁' c₀` and its non-triviality for `3 ≤ n`, `0 < c₀ < d/4`.
-/

noncomputable section

open scoped BigOperators

open Filter MeasureTheory

namespace RBM8D.Graphs

/-- A component of a deterministic kind ([II, Def 2.7 (i)]) has even scaling order: waved and
dotted edges `2`, `×`-dotted edges `0`, a `Θ` edge whose label `o` has even entries
`Σ o + 2 − 2|o|`. -/
theorem G13.even_kindOrd_of_isDetKind {V : Type*} {N : ℕ} (c : Comp V)
    (h : c.isDetKind N = true) : Even c.kind.ord := by
  obtain ⟨κ, x, y, mi, lab⟩ := c
  cases κ with
  | waved w => exact ⟨1, by simp [Kind.ord]⟩
  | dot => exact ⟨1, by simp [Kind.ord]⟩
  | xdot => exact ⟨0, by simp [Kind.ord]⟩
  | theta o =>
    simp only [Comp.isDetKind, Bool.and_eq_true, labelOK, List.all_eq_true] at h
    have key : ∀ o : List ℕ, (∀ j ∈ o, j % 2 = 0) → Even o.sum := by
      intro o
      induction o with
      | nil => intro _; exact ⟨0, rfl⟩
      | cons a t ih =>
        intro hj
        rw [List.sum_cons]
        exact (Nat.even_iff.2 (hj a List.mem_cons_self)).add
          (ih fun j hj' => hj j (List.mem_cons_of_mem a hj'))
    have ho : Even o.sum := key o fun j hj => by
      have := h.2 j hj
      simpa using this.2
    simp only [Kind.ord]
    exact (((Int.even_coe_nat _).2 ho).add even_two).sub (even_two_mul _)
  | _ => simp [Comp.isDetKind] at h

private theorem G13_even_sum_map {V : Type*} {N : ℕ} :
    ∀ cs : List (Comp V), (∀ c ∈ cs, c.isDetKind N = true) →
      Even (cs.map fun c => c.kind.ord).sum
  | [], _ => ⟨0, rfl⟩
  | c :: cs, h => by
    rw [List.map_cons, List.sum_cons]
    exact (G13.even_kindOrd_of_isDetKind c (h c List.mem_cons_self)).add
      (G13_even_sum_map cs fun c' hc => h c' (List.mem_cons_of_mem c hc))

/-- The scaling order of a deterministic graph is even ([I, (2.17)], [II, (2.6)]). -/
theorem G13.even_ord_of_isDetKind {k n N : ℕ} (Γ : Graph k n)
    (h : Γ.comps.all (Comp.isDetKind N) = true) : Even Γ.ord :=
  (G13_even_sum_map Γ.comps (List.all_eq_true.1 h)).sub (even_two_mul _)

/-- At an odd order `l` the shape of an `l`-th order self-energy forces the empty formal sum. -/
theorem G13.shape_odd_nil {l : ℕ} (hl : Odd l) {E : Expansion 2} (h : SelfEnergyShape l E) :
    E = [] := by
  rcases E with _ | ⟨g, E⟩
  · rfl
  · obtain ⟨-, hdet, hord, -⟩ := h g List.mem_cons_self
    have he := G13.even_ord_of_isDetKind g.2 hdet
    rw [hord] at he
    exact absurd ((Int.even_coe_nat l).1 he) (Nat.not_even_iff_odd.2 hl)

/-- The conclusion of `selfEnergyStepStmt` at an odd order `n`, for every variance family: the
`n`-th order `T`-equations give `Σ_n` the shape of an `n`-th order self-energy, so `Σ_n = 0`
([II, (2.6)]), which is a self-energy of every order. -/
theorem G13.selfEnergyStep_odd (d : ℕ) (Svar : VarFamily d) (n : ℕ) (hn : Odd n)
    (Sig : ℕ → Expansion 2) (E : Expansion 2) (𝒬n : ℕ → TEqRec)
    (hT : ∀ D, n < D → (𝒬n D).SigN = E ∧ IsTEquation d Svar Sig n D (𝒬n D)) :
    IsSelfEnergy d Svar (Function.update Sig n E) n := by
  obtain ⟨hE, -, -, -, -, hsh, -⟩ := hT (n + 1) (Nat.lt_succ_self n)
  rw [hE] at hsh
  obtain rfl := G13.shape_odd_nil hn hsh
  exact isSelfEnergy_nil d Svar _ n (Function.update_self ..)

/-! ## The statements of the self-energy step -/

/-- [I, (1.26)–(1.27)] for `Σ_n` at the even orders `n ≥ 4`, for the variance family `smatVar P`:
from `H(n − 1)` and `n`-th order `T`-equations over `Sig` with one `Σ_n = E` for every `D > n`,
`SelfEnergyBound` holds for the family with `Σ_n = E`. -/
def G13.boundStepStmt (d : ℕ) (P : Profile d) : Prop :=
  ∀ (Strat : ℕ → ℕ → TRec → TEqRec) (n : ℕ), 4 ≤ n → Even n →
    ∀ (Sig : ℕ → Expansion 2) (E : Expansion 2) (𝒬n : ℕ → TEqRec),
      HWith d (smatVar P) Strat Sig (n - 1) →
      (∀ D, n < D → (𝒬n D).SigN = E ∧ IsTEquation d (smatVar P) Sig n D (𝒬n D)) →
      SelfEnergyBound d (smatVar P) (Function.update Sig n E) n

/-- `selfEnergyStepStmt` for `smatVar P` from `G13.boundStepStmt`: the shape of `Σ_n` is that of
the `T`-equations, [I, (1.25)] holds for every family with `smatVar P`, and the odd orders are
`G13.selfEnergyStep_odd`. -/
theorem G13.selfEnergyStep_of_boundStep (d : ℕ) (P : Profile d) (h : G13.boundStepStmt d P) :
    selfEnergyStepStmt d (smatVar P) := by
  intro Strat n _ Sig E 𝒬n hH hT
  rcases Nat.even_or_odd n with he | ho
  · have h4 : 4 ≤ n := by
      obtain ⟨k, rfl⟩ := he
      omega
    obtain ⟨hE, -, -, -, -, hsh, -⟩ := hT (n + 1) (Nat.lt_succ_self n)
    refine ⟨?_, selfEnergySymm_smatVar d P _ n, h Strat n h4 he Sig E 𝒬n hH hT⟩
    rw [Function.update_self, ← hE]
    exact hsh
  · exact G13.selfEnergyStep_odd d (smatVar P) n ho Sig E 𝒬n hT

/-- The exponent `c₀' = ((n−3)d/2 + c₀)/(2 + (n−3)d/2 + c₀)`: the lower bound of [I, (5.39)] is
`W ≤ L^{1−c₀'}`. -/
def G13.c0w (d n : ℕ) (c₀ : ℝ) : ℝ :=
  (((n : ℝ) - 3) * d / 2 + c₀) / (2 + ((n : ℝ) - 3) * d / 2 + c₀)

/-- The exponent `c₁' = 2/(2 + (n−2)d/2 − c₀)`: the upper bound of [I, (5.39)] is
`L^{c₁'} ≤ W`. -/
def G13.c1w (d n : ℕ) (c₀ : ℝ) : ℝ := 2 / (2 + ((n : ℝ) - 2) * d / 2 - c₀)

/-- The sizes of [I, (5.39)] at order `n`: `W^{(n−3)d/2 + c₀} ≤ L²/W² ≤ W^{(n−2)d/2 − c₀}`. -/
def G13.window (d n : ℕ) (c₀ : ℝ) : Set SizeL :=
  {p | (p.1.1 : ℝ) ^ (((n : ℝ) - 3) * d / 2 + c₀) ≤ (p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2 ∧
    (p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2 ≤ (p.1.1 : ℝ) ^ (((n : ℝ) - 2) * d / 2 - c₀)}

/-- `W → ∞` along the sizes `L_n` of [I, (5.39)], inside `adm(c₀', c₁')`. -/
def G13.windowFilter (d n : ℕ) (c₀ : ℝ) : Filter SizeL :=
  admFilterL (G13.c0w d n c₀) (G13.c1w d n c₀) ⊓ Filter.principal (G13.window d n c₀)

/-! ## The window of [I, (5.39)]: monotonicity and non-triviality -/

/-- For `n ≥ 1` the sizes of [I, (5.39)] at order `n` satisfy [II, (3.15)] at order `n − 1`
with the same constant `c₀`. -/
theorem G13.window_subset_thrSet (d n : ℕ) (hn : 1 ≤ n) (c₀ : ℝ) :
    G13.window d n c₀ ⊆ thrSet d (n - 1) c₀ := by
  intro p hp
  have e : (((n - 1 : ℕ) : ℝ) - 1) * d / 2 - c₀ = ((n : ℝ) - 2) * d / 2 - c₀ := by
    rw [Nat.cast_sub hn]; push_cast; ring
  change (p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2 ≤ (p.1.1 : ℝ) ^ ((((n - 1 : ℕ) : ℝ) - 1) * d / 2 - c₀)
  rw [e]
  exact hp.2

/-- Along the sizes of [I, (5.39)] inside `adm(c₀', c₁')`, for any `c₀'`, `c₁'`, the filter of
[II, Theorem 3.6] at order `n − 1` with `c₀ᵀ = c₀` is finer: `n ≥ 1`. -/
theorem G13.admWindow_le_llFilter (d n : ℕ) (hn : 1 ≤ n) (c₀' c₁' c₀ : ℝ) :
    admFilterL c₀' c₁' ⊓ Filter.principal (G13.window d n c₀) ≤ llFilter d (n - 1) c₀' c₁' c₀ :=
  inf_le_inf_left _ (Filter.principal_mono.2 (G13.window_subset_thrSet d n hn c₀))

/-- `G13.windowFilter d n c₀` is below `llFilter d (n − 1) c₀' c₁' c₀` at the exponents
`c₀' = G13.c0w d n c₀`, `c₁' = G13.c1w d n c₀`; hence `≺` along `llFilter` implies `≺` along
`G13.windowFilter`. -/
theorem G13.windowFilter_le_llFilter (d n : ℕ) (hn : 1 ≤ n) (c₀ : ℝ) :
    G13.windowFilter d n c₀ ≤ llFilter d (n - 1) (G13.c0w d n c₀) (G13.c1w d n c₀) c₀ :=
  G13.admWindow_le_llFilter d n hn _ _ c₀

/-- A real `x ≥ 1` with `x^{(b-a)/2} ≥ 2` and `L = ⌈x^{1+a/2}⌉`: the size `(x, L)` satisfies
`x^a ≤ L²/x² ≤ x^b` and lies in `adm(a/(2+a), 2/(2+b))`, for `0 < a < b`. -/
private theorem G13_window_point (a b x : ℝ) (ha : 0 < a) (hab : a < b) (hx : 1 ≤ x)
    (hx2 : 2 ≤ x ^ ((b - a) / 2)) :
    (((⌈x ^ (1 + a / 2)⌉₊ : ℕ) : ℝ) ^ (2 / (2 + b)) ≤ x ∧
      x ≤ ((⌈x ^ (1 + a / 2)⌉₊ : ℕ) : ℝ) ^ (1 - a / (2 + a))) ∧
    (x ^ a ≤ ((⌈x ^ (1 + a / 2)⌉₊ : ℕ) : ℝ) ^ 2 / x ^ 2 ∧
      ((⌈x ^ (1 + a / 2)⌉₊ : ℕ) : ℝ) ^ 2 / x ^ 2 ≤ x ^ b) := by
  have hx0 : 0 < x := by linarith
  have h2a : 0 < 2 + a := by linarith
  have h2b : 0 < 2 + b := by linarith
  have hy1 : 1 ≤ x ^ (1 + a / 2) := Real.one_le_rpow hx (by linarith)
  have hyL : x ^ (1 + a / 2) ≤ ((⌈x ^ (1 + a / 2)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hLy : ((⌈x ^ (1 + a / 2)⌉₊ : ℕ) : ℝ) < x ^ (1 + a / 2) + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  generalize ((⌈x ^ (1 + a / 2)⌉₊ : ℕ) : ℝ) = L at hyL hLy ⊢
  have hu : x ^ (1 + b / 2) = x ^ (1 + a / 2) * x ^ ((b - a) / 2) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hyu : x ^ (1 + a / 2) + 1 ≤ x ^ (1 + b / 2) := by
    rw [hu]; nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hLu : L ≤ x ^ (1 + b / 2) := by linarith
  have hsq : ∀ c : ℝ, (x ^ c) ^ 2 = x ^ (c * 2) := fun c => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hx2' : x ^ 2 = x ^ (2 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
  have hxpos : 0 < x ^ 2 := by positivity
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · calc L ^ (2 / (2 + b)) ≤ (x ^ (1 + b / 2)) ^ (2 / (2 + b)) :=
          Real.rpow_le_rpow hL0 hLu (by positivity)
      _ = x := by
          rw [← Real.rpow_mul hx0.le]
          have : (1 + b / 2) * (2 / (2 + b)) = 1 := by field_simp
          rw [this, Real.rpow_one]
  · have h1 : 1 - a / (2 + a) = 2 / (2 + a) := by field_simp; ring
    rw [h1]
    calc x = (x ^ (1 + a / 2)) ^ (2 / (2 + a)) := by
          rw [← Real.rpow_mul hx0.le]
          have : (1 + a / 2) * (2 / (2 + a)) = 1 := by field_simp
          rw [this, Real.rpow_one]
      _ ≤ L ^ (2 / (2 + a)) := Real.rpow_le_rpow (by linarith) hyL (by positivity)
  · rw [le_div_iff₀ hxpos, hx2', ← Real.rpow_add hx0]
    calc x ^ (a + 2) = (x ^ (1 + a / 2)) ^ 2 := by rw [hsq]; congr 1; ring
      _ ≤ L ^ 2 := pow_le_pow_left₀ (by linarith) hyL 2
  · rw [div_le_iff₀ hxpos, hx2', ← Real.rpow_add hx0]
    calc L ^ 2 ≤ (x ^ (1 + b / 2)) ^ 2 := pow_le_pow_left₀ hL0 hLu 2
      _ = x ^ (b + 2) := by rw [hsq]; congr 1; ring

/-- For `0 < a < b` there is a sequence of sizes tending to `∞` in `W` inside the window
`x^a ≤ L²/x² ≤ x^b` and `adm(a/(2+a), 2/(2+b))`. -/
private theorem G13_window_tendsto (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ f : ℕ → SizeL, Tendsto f atTop (admFilterL (a / (2 + a)) (2 / (2 + b)) ⊓
      Filter.principal {p : SizeL | (p.1.1 : ℝ) ^ a ≤ (p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2 ∧
        (p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2 ≤ (p.1.1 : ℝ) ^ b}) := by
  have hδ : 0 < (b - a) / 2 := by linarith
  have hx : Tendsto (fun W : ℕ => (((W + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hev : ∀ᶠ W : ℕ in atTop, 2 ≤ (((W + 1 : ℕ) : ℝ)) ^ ((b - a) / 2) :=
    ((tendsto_rpow_atTop hδ).comp hx).eventually (eventually_ge_atTop 2)
  have hne : ∀ W : ℕ, ⌈(((W + 1 : ℕ) : ℝ)) ^ (1 + a / 2)⌉₊ ≠ 0 := fun W =>
    (Nat.ceil_pos.2 (Real.rpow_pos_of_pos (by positivity) _)).ne'
  refine ⟨fun W => ⟨(W + 1, ⌈(((W + 1 : ℕ) : ℝ)) ^ (1 + a / 2)⌉₊), hne W⟩, ?_⟩
  refine Filter.tendsto_inf.2 ⟨Filter.tendsto_comap_iff.2 (Filter.tendsto_inf.2
    ⟨Filter.tendsto_principal.2 ?_, Filter.tendsto_comap_iff.2 (tendsto_add_atTop_nat 1)⟩),
    Filter.tendsto_principal.2 ?_⟩
  · filter_upwards [hev] with W hW
    exact (G13_window_point a b _ ha hab (by exact_mod_cast Nat.le_add_left 1 W) hW).1
  · filter_upwards [hev] with W hW
    exact (G13_window_point a b _ ha hab (by exact_mod_cast Nat.le_add_left 1 W) hW).2

/-- **The sizes of [I, (5.39)] form a proper filter** for `n ≥ 3` and `0 < c₀ < d/4`: along
`L_W = ⌈W^{1+a/2}⌉`, `a = (n−3)d/2 + c₀`, the size `(W, L_W)` lies in the window and in
`adm(c₀', c₁')`, and `W → ∞`. -/
theorem G13.windowFilter_neBot_of (d n : ℕ) (hn : 3 ≤ n) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hc : c₀ < (d : ℝ) / 4) : (G13.windowFilter d n c₀).NeBot := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hprod : 0 ≤ ((n : ℝ) - 3) * d := mul_nonneg (by linarith) hd
  have ha : 0 < ((n : ℝ) - 3) * d / 2 + c₀ := by linarith
  have hab : ((n : ℝ) - 3) * d / 2 + c₀ < ((n : ℝ) - 2) * d / 2 - c₀ := by linarith
  obtain ⟨f, hf⟩ := G13_window_tendsto _ _ ha hab
  have e0 : G13.c0w d n c₀ = (((n : ℝ) - 3) * d / 2 + c₀) / (2 + (((n : ℝ) - 3) * d / 2 + c₀)) := by
    unfold G13.c0w; rw [add_assoc]
  have e1 : G13.c1w d n c₀ = 2 / (2 + (((n : ℝ) - 2) * d / 2 - c₀)) := by
    unfold G13.c1w; rw [add_sub_assoc]
  have : G13.windowFilter d n c₀ = admFilterL ((((n : ℝ) - 3) * d / 2 + c₀) /
      (2 + (((n : ℝ) - 3) * d / 2 + c₀))) (2 / (2 + (((n : ℝ) - 2) * d / 2 - c₀))) ⊓
      Filter.principal {p : SizeL | (p.1.1 : ℝ) ^ (((n : ℝ) - 3) * d / 2 + c₀) ≤
        (p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2 ∧ (p.1.2 : ℝ) ^ 2 / (p.1.1 : ℝ) ^ 2 ≤
          (p.1.1 : ℝ) ^ (((n : ℝ) - 2) * d / 2 - c₀)} := by
    unfold G13.windowFilter G13.window
    rw [e0, e1]
  rw [this]
  exact hf.neBot

end RBM8D.Graphs
