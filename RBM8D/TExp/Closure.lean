module

public import RBM8D.TExp.Defs
public import RBM8D.TExp.Second
public import RBM8D.Kernel.PropagatorSymbol

@[expose] public section

/-!
# Closure properties of `T`-expansions and the induction step

[I, (1.25)] for every family, antitonicity in the error order, congruence in the self-energy
family, monotonicity in `n`, the low orders of the solved `T`-equation, and the induction step
`H(n − 1) ⇒ H(n)` from [II, Theorem 3.7, Corollary 3.8, Lemma 3.9].
-/

noncomputable section

open scoped BigOperators

namespace RBM8D.Graphs

/-- A kernel on `Z_L^d` invariant under translations and under the reflection `x ↦ -x`. -/
def SymKer {d L : ℕ} (M : Matrix (Zd d L) (Zd d L) ℂ) : Prop :=
  TransInv M ∧ ∀ x y, M (-x) (-y) = M x y

private theorem symKer_zero {d L : ℕ} : SymKer (0 : Matrix (Zd d L) (Zd d L) ℂ) :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩

private theorem symKer_of_symm {d L : ℕ} {M : Matrix (Zd d L) (Zd d L) ℂ} (hT : TransInv M)
    (hs : ∀ x y, M x y = M y x) : SymKer M := by
  refine ⟨hT, fun x y => ?_⟩
  have := hT (-x) (-y) (x + y)
  rw [show -x + (x + y) = y by abel, show -y + (x + y) = x by abel] at this
  rw [← this, hs]

private theorem symKer_mul {d L : ℕ} [NeZero L] {M N : Matrix (Zd d L) (Zd d L) ℂ}
    (hM : SymKer M) (hN : SymKer N) : SymKer (M * N) := by
  refine ⟨TransInv_mul M N hM.1 hN.1, fun x y => ?_⟩
  simp only [Matrix.mul_apply]
  refine Fintype.sum_equiv (Equiv.neg _) _ _ fun u => ?_
  simp only [Equiv.neg_apply]
  rw [← hM.2 x (-u), ← hN.2 (-u) y, neg_neg]

private theorem transInv_cmat' {d L : ℕ} (S : Matrix (Zd d L) (Zd d L) ℝ) (hS : TransInv S) :
    TransInv (cmat S) := by
  intro x y a
  simp [cmat, hS x y a]

private theorem symKer_cmat {d L : ℕ} (S : Matrix (Zd d L) (Zd d L) ℝ) (hS : TransInv S)
    (hs : ∀ x y, S x y = S y x) : SymKer (cmat S) :=
  symKer_of_symm (transInv_cmat' S hS) fun x y => by simp [cmat, hs x y]

private theorem symKer_propagators {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ)
    (hS : TransInv S) (hs : ∀ x y, S x y = S y x) (m : ℂ) :
    SymKer (Splus m S) ∧ SymKer (Sminus m S) ∧ SymKer (cmat (Theta m S)) := by
  have hT := TransInv_propagators S hS m
  have hS' : Matrix.transpose S = S := by ext x y; exact hs y x
  have hP := transpose_propagators S hS' m
  refine ⟨symKer_of_symm hT.1 fun x y => ?_, symKer_of_symm hT.2.1 fun x y => ?_,
    symKer_of_symm (transInv_cmat' _ hT.2.2) fun x y => ?_⟩
  · exact congrFun (congrFun hP.1 y) x
  · exact congrFun (congrFun hP.2.1 y) x
  · have := congrFun (congrFun hP.2.2 y) x
    simp only [Matrix.transpose_apply] at this
    simp [cmat, this]

private theorem symKer_chain {d L : ℕ} [NeZero L] (D : Data (Zd d L)) (hTh : SymKer D.Theta)
    (hSig : ∀ l, SymKer (D.Sig l)) (o : List ℕ) : SymKer (D.chain o) := by
  unfold Data.chain
  have key : ∀ (l : List ℕ) (A : Matrix (Zd d L) (Zd d L) ℂ), SymKer A →
      SymKer (l.foldl (fun M l => M * D.Sig l * D.Theta) A) := by
    intro l
    induction l with
    | nil => intro A hA; exact hA
    | cons a l ih => intro A hA; exact ih _ (symKer_mul (symKer_mul hA (hSig a)) hTh)
  exact key o _ hTh


/-- The factor of one component of a graph on the deterministic record is unchanged when all
atoms are moved by a translation or by the reflection. -/
private theorem comp_val_act {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ)
    (hT : TransInv S) (hs : ∀ x y, S x y = S y x) (z : ℂ)
    (M : ℕ → Matrix (Zd d L) (Zd d L) ℂ) (hM : ∀ l, SymKer (M l))
    (e : Equiv.Perm (Zd d L))
    (he : ∀ K : Matrix (Zd d L) (Zd d L) ℂ, SymKer K → ∀ x y, K (e x) (e y) = K x y)
    {V : Type*} (σ : V → Zd d L) (c : Comp V) :
    Comp.val (detData S z M) (fun v => e (σ v)) c = Comp.val (detData S z M) σ c := by
  have hprop := symKer_propagators S hT hs (msc z)
  have hS := symKer_cmat S hT hs
  rcases c with ⟨kind, x, y, minor, label⟩
  cases kind with
  | G ch => cases ch <;> simp [Comp.val, detData, Charge.apply]
  | weight ch => cases ch <;> simp [Comp.val, detData, Charge.apply]
  | light ch => cases ch <;> simp [Comp.val, detData, Charge.apply]
  | inv ch => cases ch <;> simp [Comp.val, detData, Charge.apply]
  | wD ch D => cases ch <;> simp [Comp.val, detData, Charge.apply]
  | waved w =>
    cases w
    · exact he _ hS _ _
    · exact he _ hprop.1 _ _
    · exact he _ hprop.2.1 _ _
  | theta o =>
    exact he _ (symKer_chain (detData S z M) hprop.2.2 hM o) _ _
  | thetaErr n D => simp [Comp.val, detData]
  | ghost => rfl
  | aux j r b => simp [Comp.val, detData]
  | dot => simp [Comp.val, e.injective.eq_iff]
  | xdot => simp [Comp.val, e.injective.eq_iff]


/-- The value of a graph on the deterministic record is unchanged when all external atoms are
moved by a translation or by the reflection. -/
private theorem graph_val_act {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ)
    (hT : TransInv S) (hs : ∀ x y, S x y = S y x) (z : ℂ)
    (M : ℕ → Matrix (Zd d L) (Zd d L) ℂ) (hM : ∀ l, SymKer (M l))
    (e : Equiv.Perm (Zd d L))
    (he : ∀ K : Matrix (Zd d L) (Zd d L) ℂ, SymKer K → ∀ x y, K (e x) (e y) = K x y)
    {k n : ℕ} (Γ : Graph k n) (x : Fin k → Zd d L) :
    Γ.val (detData S z M) (fun i => e (x i)) = Γ.val (detData S z M) x := by
  unfold Graph.val
  symm
  refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin n)) e) _ _ fun s => ?_
  unfold Graph.term
  congr 1
  have h1 : Sum.elim (fun i => e (x i)) (Equiv.arrowCongr (Equiv.refl (Fin n)) e s) =
      fun u => e (Sum.elim x s u) := by
    funext u
    cases u <;> rfl
  rw [h1]
  congr 1
  exact (List.map_congr_left fun c _ =>
    comp_val_act S hT hs z M hM e he (Sum.elim x s) c).symm

/-- The value of a formal sum on the deterministic record is unchanged when all external atoms
are moved by a translation or by the reflection. -/
private theorem expansion_val_act {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ)
    (hT : TransInv S) (hs : ∀ x y, S x y = S y x) (z : ℂ)
    (M : ℕ → Matrix (Zd d L) (Zd d L) ℂ) (hM : ∀ l, SymKer (M l))
    (e : Equiv.Perm (Zd d L))
    (he : ∀ K : Matrix (Zd d L) (Zd d L) ℂ, SymKer K → ∀ x y, K (e x) (e y) = K x y)
    {k : ℕ} (E : Expansion k) (x : Fin k → Zd d L) :
    E.val (detData S z M) (fun i => e (x i)) = E.val (detData S z M) x := by
  unfold Expansion.val
  congr 1
  exact List.map_congr_left fun g _ => graph_val_act S hT hs z M hM e he g.2 x

/-- The matrix of values of a formal sum in two external atoms is translation invariant and
reflection invariant. -/
theorem symKer_val {d L : ℕ} [NeZero L] (S : Matrix (Zd d L) (Zd d L) ℝ)
    (hT : TransInv S) (hs : ∀ x y, S x y = S y x) (z : ℂ)
    (M : ℕ → Matrix (Zd d L) (Zd d L) ℂ) (hM : ∀ l, SymKer (M l)) (E : Expansion 2) :
    SymKer (Matrix.of fun x y => E.val (detData S z M) ![x, y]) := by
  refine ⟨fun x y a => ?_, fun x y => ?_⟩
  · have := expansion_val_act S hT hs z M hM (Equiv.addRight a) (fun K hK u v => hK.1 u v a) E
      ![x, y]
    simp only [Matrix.of_apply]
    rw [← this]
    congr 1
    funext i
    fin_cases i <;> rfl
  · have := expansion_val_act S hT hs z M hM (Equiv.neg _) (fun K hK u v => hK.2 u v) E ![x, y]
    simp only [Matrix.of_apply]
    rw [← this]
    congr 1
    funext i
    fin_cases i <;> rfl

/-- The self-energy matrices below order `N` are translation invariant and reflection
invariant. -/
private theorem symKer_sigUpTo {d L : ℕ} [NeZero L] (Sig : ℕ → Expansion 2)
    (S : Matrix (Zd d L) (Zd d L) ℝ) (hT : TransInv S) (hs : ∀ x y, S x y = S y x) (z : ℂ) :
    ∀ N k, SymKer (sigUpTo Sig S z N k) := by
  intro N
  induction N with
  | zero => intro k; exact symKer_zero
  | succ N ih =>
    intro k
    simp only [sigUpTo]
    by_cases hk : k = N
    · subst hk
      rw [Function.update_self]
      exact symKer_val S hT hs z _ ih (Sig k)
    · rw [Function.update_of_ne hk]
      exact ih k


/-- [I, (1.25)] for every formal sum: if every variance matrix `Svar W L` is translation invariant
and symmetric, then for every family `Sig`, every `l`, every `(W, L)` and every `z` with
`Im z > 0`, `Σ_l(x, x + a) = Σ_l(0, a)` and `Σ_l(0, a) = Σ_l(0, -a)`. -/
theorem selfEnergySymm :
  ∀ (d : ℕ) (Svar : VarFamily d) (Sig : ℕ → Expansion 2) (l : ℕ),
    (∀ (W L : ℕ) [NeZero L], TransInv (Svar W L) ∧ ∀ x y, Svar W L x y = Svar W L y x) →
    SelfEnergySymm d Svar Sig l := by
  intro d Svar Sig l h W L _ z _ x a
  obtain ⟨hT, hs⟩ := h W L
  have hK : SymKer (sigMat Sig (Svar W L) z l) :=
    symKer_val (Svar W L) hT hs z _ (symKer_sigUpTo Sig (Svar W L) hT hs z l) (Sig l)
  refine ⟨?_, ?_⟩
  · have := hK.1 0 a x
    rw [zero_add, add_comm a x] at this
    exact this
  · have := hK.2 0 (-a)
    rw [neg_zero, neg_neg] at this
    exact this

/-- The matrices `sigUpTo` of two families agree below `N` when the families agree below `N`. -/
private theorem sigUpTo_congr {ι : Type} [Fintype ι] [DecidableEq ι] (Sig Sig' : ℕ → Expansion 2)
    (S : Matrix ι ι ℝ) (z : ℂ) :
    ∀ N : ℕ, (∀ k < N, Sig' k = Sig k) → sigUpTo Sig' S z N = sigUpTo Sig S z N := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro h
    have h1 : sigUpTo Sig' S z N = sigUpTo Sig S z N := ih fun k hk => h k (by omega)
    simp only [sigUpTo, h1, h N (by omega)]

/-- `Σ_l` depends only on `Sig 0, …, Sig l`. -/
private theorem sigMat_congr {ι : Type} [Fintype ι] [DecidableEq ι] (Sig Sig' : ℕ → Expansion 2)
    (S : Matrix ι ι ℝ) (z : ℂ) (l : ℕ) (h : ∀ k ≤ l, Sig' k = Sig k) :
    sigMat Sig' S z l = sigMat Sig S z l := by
  simp only [sigMat, sigUpTo_congr Sig Sig' S z l (fun k hk => h k hk.le), h l le_rfl]

/-- Being a self-energy of order `l` depends only on `Sig 0, …, Sig l`. -/
private theorem isSelfEnergy_congr (d : ℕ) (Svar : VarFamily d) (Sig Sig' : ℕ → Expansion 2)
    (l : ℕ) (h : ∀ k ≤ l, Sig' k = Sig k) :
    IsSelfEnergy d Svar Sig l → IsSelfEnergy d Svar Sig' l := by
  have hm : ∀ (W L : ℕ) [NeZero L] (z : ℂ),
      sigMat Sig' (Svar W L) z l = sigMat Sig (Svar W L) z l :=
    fun W L _ z => sigMat_congr Sig Sig' (Svar W L) z l h
  rintro ⟨hsh, hsy, hbd⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h l le_rfl]; exact hsh
  · unfold SelfEnergySymm
    simp only [hm]
    exact hsy
  · unfold SelfEnergyBound
    simp only [hm]
    exact hbd

private theorem selfEnergiesUpTo_congr (d : ℕ) (Svar : VarFamily d) (Sig Sig' : ℕ → Expansion 2)
    (n : ℕ) (h : ∀ k ≤ n, Sig' k = Sig k) :
    SelfEnergiesUpTo d Svar Sig n → SelfEnergiesUpTo d Svar Sig' n :=
  fun H k hk4 hkn hke =>
    isSelfEnergy_congr d Svar Sig Sig' k (fun j hj => h j (hj.trans hkn)) (H k hk4 hkn hke)

private theorem sigConsistent_congr {ι : Type} [Fintype ι] [DecidableEq ι]
    (Sig Sig' : ℕ → Expansion 2) (N : ℕ) (D : Data ι) (h : ∀ k < N, Sig' k = Sig k) :
    SigConsistent Sig' N D → SigConsistent Sig N D :=
  fun H k hk4 hkN hke => by rw [← h k hkN]; exact H k hk4 hkN hke

private theorem shapesUpTo_congr (Sig Sig' : ℕ → Expansion 2) (n : ℕ)
    (h : ∀ k, 4 ≤ k → k ≤ n → Sig' k = Sig k) :
    SelfEnergyShapesUpTo Sig n → SelfEnergyShapesUpTo Sig' n :=
  fun H k hk4 hkn hke => by rw [h k hk4 hkn]; exact H k hk4 hkn hke

/-- The structural part of an `n`-th order `T`-equation ([II, Def 3.3], [II, Def 6.3]) depends
only on `Sig 0, …, Sig (n - 1)`. -/
theorem isTEqStruct_congr :
  ∀ (Sig Sig' : ℕ → Expansion 2) (n D : ℕ) (𝒬 : TEqRec), (∀ k < n, Sig' k = Sig k) →
    𝒬.IsTEqStruct Sig n D → 𝒬.IsTEqStruct Sig' n D := by
  intro Sig Sig' n D 𝒬 h ⟨h1, hid, hsh, h4, h5, h6, h7⟩
  refine ⟨h1, ?_, shapesUpTo_congr Sig Sig' (n - 1) (fun k hk4 hk => h k (by omega)) hsh,
    h4, h5, h6, h7⟩
  intro Ω ι _ _ PF D' hA hcons e ω
  exact hid Ω ι PF D' hA (fun ω' => sigConsistent_congr Sig Sig' n _ h (hcons ω')) e ω

/-- The structural part of a `T`-expansion of order `n` depends only on `Sig 0, …, Sig n`. -/
private theorem isTExpStruct_congr (Sig Sig' : ℕ → Expansion 2) (n D : ℕ) (𝒯 : TRec)
    (h : ∀ k ≤ n, Sig' k = Sig k) : 𝒯.IsTExpStruct Sig n D → 𝒯.IsTExpStruct Sig' n D := by
  rintro ⟨h1, hid, hsh, h4, h5⟩
  refine ⟨h1, ?_, shapesUpTo_congr Sig Sig' n (fun k _ hk => h k hk) hsh, h4, h5⟩
  intro Ω ι _ _ PF D' hA hcons e ω
  exact hid Ω ι PF D' hA
    (fun ω' => sigConsistent_congr Sig Sig' (n + 1) _ (fun k hk => h k (by omega)) (hcons ω')) e ω

/-- The families of `H(n)` for `Sig` are families of `H(n)` for every `Sig'` that agrees with
`Sig` up to order `n`. -/
theorem hFam_congr :
  ∀ (Strat : ℕ → ℕ → TRec → TEqRec) (Sig Sig' : ℕ → Expansion 2) (n : ℕ)
    (𝒬 : ℕ → ℕ → TEqRec) (𝒯 : ℕ → ℕ → TRec), (∀ k ≤ n, Sig' k = Sig k) →
    HFam Strat Sig n 𝒬 𝒯 → HFam Strat Sig' n 𝒬 𝒯 := by
  intro Strat Sig Sig' n 𝒬 𝒯 h ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨fun k D hk2 hkn hkD => ?_, fun k D hk3 hkn hkD => ?_, h3, h4, h5, h6⟩
  · obtain ⟨a, b, c, e⟩ := h1 k D hk2 hkn hkD
    exact ⟨isTEqStruct_congr Sig Sig' k D _ (fun j hj => h j (by omega)) a,
      isTExpStruct_congr Sig Sig' k D _ (fun j hj => h j (by omega)) b, c, e⟩
  · rw [h2 k D hk3 hkn hkD, h k hkn]

/-- `H(n)` for the construction `Strat` depends only on `Sig 0, …, Sig n`. -/
theorem hWith_congr :
  ∀ (d : ℕ) (Svar : VarFamily d) (Strat : ℕ → ℕ → TRec → TEqRec) (Sig Sig' : ℕ → Expansion 2)
    (n : ℕ), (∀ k ≤ n, Sig' k = Sig k) →
    (HWith d Svar Strat Sig n ↔ HWith d Svar Strat Sig' n) := by
  intro d Svar Strat Sig Sig' n h
  have key : ∀ (A B : ℕ → Expansion 2), (∀ k ≤ n, B k = A k) →
      HWith d Svar Strat A n → HWith d Svar Strat B n := by
    intro A B hAB ⟨hse, 𝒬, 𝒯, hf⟩
    exact ⟨selfEnergiesUpTo_congr d Svar A B n hAB hse, 𝒬, 𝒯, hFam_congr Strat A B n 𝒬 𝒯 hAB hf⟩
  exact ⟨key Sig Sig' h, key Sig' Sig fun k hk => (h k hk).symm⟩

/-- One family of self-energies for all orders from `H(2)` and the induction step: if `H(2)`
holds for some family and `H(n - 1) ⇒ H(n)` holds for every `n ≥ 3`, then there is a single `Sig`
with `H(n)` for every `n ≥ 2` ([II, Theorem 3.7, Corollary 3.8, Lemma 3.9]). -/
theorem jointH_of_step :
  ∀ (d : ℕ) (Svar : VarFamily d) (Strat : ℕ → ℕ → TRec → TEqRec),
    (∃ Sig : ℕ → Expansion 2, HWith d Svar Strat Sig 2) → inductionStepStmt d Svar Strat →
    jointHStmt d Svar Strat := by
  intro d Svar Strat ⟨Sig₀, h₀⟩ hstep
  classical
  let nxt : ∀ m : ℕ, {S : ℕ → Expansion 2 // HWith d Svar Strat S (m + 2)} →
      {S : ℕ → Expansion 2 // HWith d Svar Strat S (m + 3)} := fun m s =>
    ⟨Function.update s.1 (m + 3)
        (Classical.choose
          (hstep (m + 3) (by omega) s.1 (show HWith d Svar Strat s.1 (m + 3 - 1) from s.2))),
      Classical.choose_spec
        (hstep (m + 3) (by omega) s.1 (show HWith d Svar Strat s.1 (m + 3 - 1) from s.2))⟩
  let T : ∀ m : ℕ, {S : ℕ → Expansion 2 // HWith d Svar Strat S (m + 2)} := fun m =>
    Nat.rec (motive := fun m => {S : ℕ → Expansion 2 // HWith d Svar Strat S (m + 2)})
      ⟨Sig₀, h₀⟩ (fun m s => nxt m s) m
  have hstable : ∀ i j, i ≤ j → ∀ k ≤ i + 2, (T i).1 k = (T j).1 k := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro k _; rfl
    | succ j hij ih =>
      intro k hk
      rw [ih k hk]
      change (T j).1 k = Function.update (T j).1 (j + 3) _ k
      rw [Function.update_of_ne (by omega)]
  refine ⟨fun k => (T k).1 k, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  refine (hWith_congr d Svar Strat (T m).1 _ (m + 2) fun k hk => ?_).1 (T m).2
  by_cases hkm : k ≤ m
  · exact hstable k m hkm k (by omega)
  · exact (hstable m k (by omega) k hk).symm


private def labelInc (o : List ℕ) : ℕ := (o.map (· - 2)).sum

private theorem mem_chainLabelsAux_succ {f b : ℕ} {o : List ℕ} :
    o ∈ chainLabelsAux (f + 1) b ↔ ∃ j, j ≤ b ∧ 2 ≤ j ∧ j % 2 = 0 ∧
      (o = [j + 2] ∨ ∃ o' ∈ chainLabelsAux f (b - j), (j + 2) :: o' = o) := by
  simp only [chainLabelsAux, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_cons,
    List.mem_map, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨j, ⟨hj, h2, h3⟩, h⟩
    exact ⟨j, by omega, h2, h3, h⟩
  · rintro ⟨j, hj, h2, h3, h⟩
    exact ⟨j, ⟨by omega, h2, h3⟩, h⟩

private theorem chainLabelsAux_ne_nil : ∀ f b, ∀ o ∈ chainLabelsAux f b, o ≠ [] := by
  intro f
  induction f with
  | zero => intro b o ho; simp [chainLabelsAux] at ho
  | succ f ih =>
    intro b o ho
    obtain ⟨j, -, -, -, h | ⟨o', -, h⟩⟩ := mem_chainLabelsAux_succ.1 ho <;> subst h <;> simp

private theorem chainLabelsAux_entries :
    ∀ f b, ∀ o ∈ chainLabelsAux f b, ∀ e ∈ o, 4 ≤ e ∧ e % 2 = 0 := by
  intro f
  induction f with
  | zero => intro b o ho; simp [chainLabelsAux] at ho
  | succ f ih =>
    intro b o ho e he
    obtain ⟨j, -, h2, h3, h | ⟨o', ho', h⟩⟩ := mem_chainLabelsAux_succ.1 ho <;> subst h
    · obtain rfl : e = j + 2 := by simpa using he
      omega
    · rcases List.mem_cons.1 he with rfl | he
      · omega
      · exact ih _ o' ho' e he

/-- The excess of `(j+2) :: o`. -/
private theorem labelInc_cons (j : ℕ) (o : List ℕ) : labelInc ((j + 2) :: o) = j + labelInc o := by
  simp [labelInc]

private theorem range_filter_le (P : ℕ → Bool) (b b' : ℕ) (hb : b ≤ b') :
    (List.range (b' + 1)).filter (fun a => decide (a ≤ b) && P a) =
      (List.range (b + 1)).filter P := by
  induction b', hb using Nat.le_induction with
  | base =>
    refine List.filter_congr fun a ha => ?_
    have := List.mem_range.1 ha
    simp [show a ≤ b by omega]
  | succ b' hb ih =>
    rw [List.range_succ, List.filter_append, ih]
    simp [show ¬ (b' + 1 ≤ b) by omega]

private theorem flatMap_ite_nil {α β : Type} (l : List α) (p : α → Prop) [DecidablePred p]
    (F : α → List β) :
    l.flatMap (fun a => if p a then F a else []) = (l.filter fun a => decide (p a)).flatMap F := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a <;> simp [h, ih]

private theorem chainLabelsAux_sub : ∀ f f' b b', f ≤ f' → b ≤ b' →
    (chainLabelsAux f' b').filter (fun o => decide (o.length ≤ f ∧ labelInc o ≤ b)) =
      chainLabelsAux f b := by
  intro f
  induction f with
  | zero =>
    intro f' b b' _ _
    have e0 : chainLabelsAux 0 b = [] := rfl
    rw [e0, List.filter_eq_nil_iff]
    intro o ho
    have := chainLabelsAux_ne_nil f' b' o ho
    simp only [decide_eq_true_eq]
    intro h
    exact this (List.length_eq_zero_iff.1 (by omega))
  | succ f ih =>
    intro f' b b' hf hb
    obtain ⟨f'', rfl⟩ : ∃ f'', f' = f'' + 1 := ⟨f' - 1, by omega⟩
    have hΦ : ∀ j, ([j + 2] :: (chainLabelsAux f'' (b' - j)).map ((j + 2) :: ·)).filter
        (fun o => decide (o.length ≤ f + 1 ∧ labelInc o ≤ b)) =
          if j ≤ b then [j + 2] :: (chainLabelsAux f (b - j)).map ((j + 2) :: ·) else [] := by
      intro j
      by_cases hjb : j ≤ b
      · have h1 : decide (([j + 2] : List ℕ).length ≤ f + 1 ∧ labelInc [j + 2] ≤ b) = true := by
          simp [labelInc, hjb]
        simp only [hjb, ↓reduceIte, List.filter_cons, h1, List.filter_map]
        rw [← ih f'' (b - j) (b' - j) (by omega) (by omega)]
        congr 2
        refine List.filter_congr fun o _ => ?_
        simp only [Function.comp, List.length_cons, labelInc_cons, decide_eq_decide]
        omega
      · have h1 : decide (([j + 2] : List ℕ).length ≤ f + 1 ∧ labelInc [j + 2] ≤ b) = false := by
          have hl : labelInc [j + 2] = j := by simp [labelInc]
          simp only [hl, decide_eq_false_iff_not, not_and, not_le]
          intro _
          omega
        simp only [hjb, ↓reduceIte, List.filter_cons, h1, Bool.false_eq_true,
          List.filter_eq_nil_iff, List.mem_map]
        rintro o ⟨o', -, rfl⟩
        simp only [labelInc_cons, decide_eq_true_eq, not_and, not_le]
        intro _
        omega
    simp only [chainLabelsAux, List.filter_flatMap]
    simp only [hΦ, flatMap_ite_nil, List.filter_filter]
    rw [range_filter_le (fun j => decide (2 ≤ j) && j % 2 == 0) b b' hb]

/-- The excess of a label with entries `≥ 2` as an integer. -/
private theorem labelInc_cast : ∀ o : List ℕ, (∀ e ∈ o, 2 ≤ e) →
    ((labelInc o : ℕ) : ℤ) = (o.sum : ℤ) - 2 * o.length := by
  intro o
  induction o with
  | nil => intro _; simp [labelInc]
  | cons e o ih =>
    intro h
    have h1 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have h2 := h e (List.mem_cons_self ..)
    have h3 : labelInc (e :: o) = (e - 2) + labelInc o := by simp [labelInc]
    rw [h3, Nat.cast_add, Nat.cast_sub h2, h1, List.sum_cons, List.length_cons]
    push_cast
    ring

private theorem length_le_labelInc : ∀ o : List ℕ, (∀ e ∈ o, 4 ≤ e) → o.length ≤ labelInc o := by
  intro o
  induction o with
  | nil => intro _; simp
  | cons e o ih =>
    intro h
    have h1 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have h2 := h e (List.mem_cons_self ..)
    have : labelInc (e :: o) = (e - 2) + labelInc o := by simp [labelInc]
    simp only [List.length_cons, this]
    omega

private theorem chainLabels_entries (n : ℕ) : ∀ o ∈ chainLabels n, ∀ e ∈ o, 4 ≤ e :=
  fun o ho e he => (chainLabelsAux_entries _ _ o ho e he).1

/-- The labels of `chainLabels n` with a given excess `≤ n - 2` do not depend on `n`. -/
private theorem chainLabels_filter (n n' : ℕ) (hn : n ≤ n') (p : List ℕ → Bool)
    (hp : ∀ o ∈ chainLabels n', p o = true → labelInc o + 2 ≤ n) :
    (chainLabels n).filter p = (chainLabels n').filter p := by
  have h := chainLabelsAux_sub (n - 2) (n' - 2) (n - 2) (n' - 2) (by omega) (by omega)
  rw [chainLabels, chainLabels, ← h, List.filter_filter]
  refine List.filter_congr fun o ho => ?_
  by_cases hpo : p o = true
  · have h1 := hp o ho hpo
    have h2 : o.length ≤ labelInc o :=
      length_le_labelInc o fun e he => (chainLabelsAux_entries _ _ o ho e he).1
    simp [hpo]
    omega
  · have : p o = false := by simpa using hpo
    simp [this]

/-- The scaling order of a graph with the `Θ` edge at `⊗` relabelled. -/
private theorem ord_relabelRoot {n : ℕ} (Γ : Graph 3 n) (hΓ : Γ.ThetaRooted) (o : List ℕ) :
    (Γ.relabelRoot o).ord = Γ.ord + ((o.sum : ℤ) - 2 * o.length) := by
  obtain ⟨j, v, -, hk, -, -, hxy, hrest, -⟩ := hΓ
  have hl : Γ.comps = Γ.comps.take j ++ Γ.comps[j] :: Γ.comps.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j Γ.comps, List.drop_eq_getElem_cons j.2]
    rfl
  have hrest' : ∀ c ∈ Γ.comps.take j ++ Γ.comps.drop (j + 1), c.x ≠ .inl 0 ∧ c.y ≠ .inl 0 := by
    intro c hc
    have h := hrest c (by simpa [Graph.dropComp, List.eraseIdx_eq_take_drop_succ] using hc)
    exact ⟨h.1, h.2.1⟩
  have hx : Γ.comps[j].x = .inl 0 ∨ Γ.comps[j].y = .inl 0 := Or.inl hxy.1
  have hrel : (Γ.relabelRoot o).comps = Γ.comps.map fun c =>
      if c.kind = .theta [] ∧ (c.x = .inl 0 ∨ c.y = .inl 0) then { c with kind := Kind.theta o }
      else c := rfl
  generalize Γ.comps.take j = A at hl hrest'
  generalize Γ.comps.drop (j + 1) = B at hl hrest'
  generalize Γ.comps[j] = cj at hl hk hx
  simp only [Graph.ord]
  rw [hrel, hl]
  have hρ : ∀ c ∈ A ++ B,
      (if c.kind = .theta [] ∧ (c.x = .inl 0 ∨ c.y = .inl 0) then { c with kind := Kind.theta o }
        else c) = c := by
    intro c hc
    have := hrest' c hc
    have hn : ¬ (c.kind = .theta [] ∧ (c.x = .inl 0 ∨ c.y = .inl 0)) := by
      rintro ⟨-, h | h⟩
      · exact this.1 h
      · exact this.2 h
    simp only [hn, ↓reduceIte]
  have hmapA : A.map (fun c => if c.kind = .theta [] ∧ (c.x = .inl 0 ∨ c.y = .inl 0)
      then { c with kind := Kind.theta o } else c) = A := by
    conv_rhs => rw [← List.map_id A]
    exact List.map_congr_left fun c hc => hρ c (List.mem_append_left _ hc)
  have hmapB : B.map (fun c => if c.kind = .theta [] ∧ (c.x = .inl 0 ∨ c.y = .inl 0)
      then { c with kind := Kind.theta o } else c) = B := by
    conv_rhs => rw [← List.map_id B]
    exact List.map_congr_left fun c hc => hρ c (List.mem_append_right _ hc)
  have hρj : (if cj.kind = .theta [] ∧ (cj.x = .inl 0 ∨ cj.y = .inl 0)
      then { cj with kind := Kind.theta o } else cj) = { cj with kind := Kind.theta o } :=
    by simp only [hk, hx, and_self, ↓reduceIte]
  simp only [List.map_append, List.map_cons, hmapA, hmapB, hρj, List.sum_append, List.sum_cons]
  simp only [hk, Kind.ord, List.sum_nil, List.length_nil]
  push_cast
  ring

/-- The graphs obtained from `g` by relabelling the `Θ` edge at `⊗` with the plain label and the
labels of `chainLabels n`. -/
private def relabels (n : ℕ) (g : Σ m : ℕ, Graph 3 m) : List (Σ m : ℕ, Graph 3 m) :=
  ([] :: chainLabels n).map fun o => ⟨g.1, g.2.relabelRoot o⟩

private theorem solveLow_R (n : ℕ) (𝒬 : TEqRec) : (𝒬.solveLow n).R = 𝒬.R.flatMap (relabels n) := rfl

private theorem solveLow_Q (n : ℕ) (𝒬 : TEqRec) : (𝒬.solveLow n).Q = 𝒬.Q.flatMap (relabels n) := rfl

private theorem inc_nonneg (n : ℕ) : ∀ o ∈ ([] :: chainLabels n),
    0 ≤ (o.sum : ℤ) - 2 * o.length := by
  intro o ho
  rcases List.mem_cons.1 ho with rfl | ho
  · simp
  · have h1 := chainLabels_entries n o ho
    have h2 := labelInc_cast o fun e he => by have := h1 e he; omega
    omega

private theorem relabels_filter_nil (n : ℕ) (g : Σ m : ℕ, Graph 3 m) (hg : g.2.ThetaRooted)
    (j : ℤ) (hj : j < g.2.ord) :
    (relabels n g).filter (fun h => decide (h.2.ord = j)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro h hh
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hh
  have := inc_nonneg n o ho
  simp only [ord_relabelRoot g.2 hg o, decide_eq_true_eq]
  omega

private theorem relabels_filter_eq (n n' : ℕ) (hn : n ≤ n') (g : Σ m : ℕ, Graph 3 m)
    (hg : g.2.ThetaRooted) (hg2 : 2 ≤ g.2.ord) (j : ℕ) (hj : j ≤ n) :
    (relabels n g).filter (fun h => decide (h.2.ord = (j : ℤ))) =
      (relabels n' g).filter (fun h => decide (h.2.ord = (j : ℤ))) := by
  unfold relabels
  rw [List.filter_map, List.filter_map]
  congr 1
  have hp : ∀ o, ((fun h : (Σ m : ℕ, Graph 3 m) => decide (h.2.ord = (j : ℤ))) ∘
      fun o : List ℕ => (⟨g.1, g.2.relabelRoot o⟩ : Σ m : ℕ, Graph 3 m)) o =
        decide (g.2.ord + ((o.sum : ℤ) - 2 * o.length) = j) := by
    intro o
    simp only [Function.comp, ord_relabelRoot g.2 hg o]
  rw [List.filter_congr (fun o _ => hp o), List.filter_congr (fun o _ => hp o)]
  have key : (chainLabels n).filter
      (fun o => decide (g.2.ord + ((o.sum : ℤ) - 2 * o.length) = j)) =
        (chainLabels n').filter (fun o => decide (g.2.ord + ((o.sum : ℤ) - 2 * o.length) = j)) := by
    refine chainLabels_filter n n' hn _ fun o ho hpo => ?_
    have h1 := chainLabels_entries n' o ho
    have h2 := labelInc_cast o fun e he => by have := h1 e he; omega
    simp only [decide_eq_true_eq] at hpo
    omega
  simp only [List.filter_cons, key]

private theorem flatMap_eq_flatMap_filter {α β : Type*} (l : List α) (p : α → Bool)
    (f : α → List β) (h : ∀ x ∈ l, p x = false → f x = []) :
    l.flatMap f = (l.filter p).flatMap f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    by_cases hx : p x = true
    · simp [hx, ih']
    · have hx' : p x = false := by simpa using hx
      simp [hx', h x (List.mem_cons_self ..) hx', ih']

private theorem filter_le_perm_aux {α : Type*} (f : α → ℤ) (J : ℕ) (l : List α) :
    (l.filter fun x => decide (f x ≤ ((J + 1 : ℕ) : ℤ))).Perm
      ((l.filter fun x => decide (f x ≤ (J : ℤ))) ++
        l.filter fun x => decide (f x = ((J + 1 : ℕ) : ℤ))) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    by_cases h1 : f x ≤ (J : ℤ)
    · have d1 : decide (f x ≤ (J : ℤ)) = true := by simpa using h1
      have d2 : decide (f x ≤ ((J + 1 : ℕ) : ℤ)) = true := by simp; omega
      have d3 : decide (f x = ((J + 1 : ℕ) : ℤ)) = false := by simp; omega
      simp only [List.filter_cons, d1, d2, d3, ↓reduceIte, List.cons_append]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih.cons x
    · by_cases h3 : f x = ((J + 1 : ℕ) : ℤ)
      · have d1 : decide (f x ≤ (J : ℤ)) = false := by simp; omega
        have d2 : decide (f x ≤ ((J + 1 : ℕ) : ℤ)) = true := by simp; omega
        have d3 : decide (f x = ((J + 1 : ℕ) : ℤ)) = true := by simpa using h3
        simp only [List.filter_cons, d1, d2, d3, ↓reduceIte, Bool.false_eq_true]
        exact (ih.cons x).trans List.perm_middle.symm
      · have d1 : decide (f x ≤ (J : ℤ)) = false := by simp; omega
        have d2 : decide (f x ≤ ((J + 1 : ℕ) : ℤ)) = false := by simp; omega
        have d3 : decide (f x = ((J + 1 : ℕ) : ℤ)) = false := by simpa using h3
        simp only [List.filter_cons, d1, d2, d3, Bool.false_eq_true, ↓reduceIte]
        exact ih

private theorem perm_filter_le {α : Type*} (f : α → ℤ) (l₁ l₂ : List α)
    (hge : ∀ x ∈ l₁ ++ l₂, 0 < f x) (J : ℕ)
    (h : ∀ i : ℕ, i ≤ J → (l₁.filter fun x => decide (f x = (i : ℤ))).Perm
      (l₂.filter fun x => decide (f x = (i : ℤ)))) :
    (l₁.filter fun x => decide (f x ≤ (J : ℤ))).Perm
      (l₂.filter fun x => decide (f x ≤ (J : ℤ))) := by
  induction J with
  | zero =>
    have e : ∀ l : List α, (∀ x ∈ l, 0 < f x) →
        (l.filter fun x => decide (f x ≤ ((0 : ℕ) : ℤ))) = [] := by
      intro l hl
      rw [List.filter_eq_nil_iff]
      intro x hx
      have := hl x hx
      simp only [decide_eq_true_eq]
      omega
    rw [e l₁ fun x hx => hge x (List.mem_append_left _ hx),
      e l₂ fun x hx => hge x (List.mem_append_right _ hx)]
  | succ J ih =>
    refine (filter_le_perm_aux f J l₁).trans (List.Perm.trans ?_ (filter_le_perm_aux f J l₂).symm)
    exact (ih fun i hi => h i (by omega)).append (h (J + 1) le_rfl)

private theorem flatMap_relabels_perm (n n' : ℕ) (hnn' : n ≤ n') (k : ℕ) (hk : k ≤ n)
    (l₁ l₂ : List (Σ m : ℕ, Graph 3 m))
    (h1 : ∀ g ∈ l₁, g.2.ThetaRooted ∧ 2 ≤ g.2.ord)
    (h2 : ∀ g ∈ l₂, g.2.ThetaRooted ∧ 2 ≤ g.2.ord)
    (hc : ∀ i : ℕ, i ≤ k → (l₁.filter fun g => decide (g.2.ord = (i : ℤ))).Perm
      (l₂.filter fun g => decide (g.2.ord = (i : ℤ))))
    (j : ℕ) (hj : j ≤ k) :
    ((l₁.flatMap (relabels n)).filter fun g => decide (g.2.ord = (j : ℤ))).Perm
      ((l₂.flatMap (relabels n')).filter fun g => decide (g.2.ord = (j : ℤ))) := by
  rw [List.filter_flatMap, List.filter_flatMap]
  have e2 : l₂.flatMap (fun g => (relabels n' g).filter fun g => decide (g.2.ord = (j : ℤ))) =
      l₂.flatMap (fun g => (relabels n g).filter fun g => decide (g.2.ord = (j : ℤ))) :=
    List.flatMap_congr fun g hg =>
      (relabels_filter_eq n n' hnn' g (h2 g hg).1 (h2 g hg).2 j (by omega)).symm
  rw [e2]
  have hle : ∀ l : List (Σ m : ℕ, Graph 3 m), (∀ g ∈ l, g.2.ThetaRooted) →
      l.flatMap (fun g => (relabels n g).filter fun g => decide (g.2.ord = (j : ℤ))) =
        (l.filter fun g => decide (g.2.ord ≤ (j : ℤ))).flatMap
          (fun g => (relabels n g).filter fun g => decide (g.2.ord = (j : ℤ))) := by
    intro l hl
    refine flatMap_eq_flatMap_filter l _ _ fun g hg hp => ?_
    exact relabels_filter_nil n g (hl g hg) j (by simpa using hp)
  rw [hle l₁ fun g hg => (h1 g hg).1, hle l₂ fun g hg => (h2 g hg).1]
  refine List.Perm.flatMap_right _ (perm_filter_le (fun g => g.2.ord) l₁ l₂ ?_ j
    fun i hi => hc i (by omega))
  intro g hg
  rcases List.mem_append.1 hg with hg | hg
  · have := (h1 g hg).2; change 0 < g.2.ord; omega
  · have := (h2 g hg).2; change 0 < g.2.ord; omega


private theorem coherent_symm {k : ℕ} {a b : TRec} (h : TRec.Coherent k a b) :
    TRec.Coherent k b a :=
  fun j hj => ⟨(h j hj).1.symm, (h j hj).2.symm⟩


private theorem solveLow_coherent_le (k n n' : ℕ) (𝒬 𝒬' : TEqRec) (hkn : k ≤ n) (hnn' : n ≤ n')
    (h1 : ∀ g ∈ 𝒬.R ++ 𝒬.Q, g.2.ThetaRooted ∧ 2 ≤ g.2.ord)
    (h2 : ∀ g ∈ 𝒬'.R ++ 𝒬'.Q, g.2.ThetaRooted ∧ 2 ≤ g.2.ord)
    (hc : TRec.Coherent k 𝒬.toTRec 𝒬'.toTRec) :
    TRec.Coherent k (𝒬.solveLow n) (𝒬'.solveLow n') := by
  intro j hj
  refine ⟨?_, ?_⟩
  · rw [solveLow_R, solveLow_R]
    exact flatMap_relabels_perm n n' hnn' k hkn _ _
      (fun g hg => h1 g (List.mem_append_left _ hg)) (fun g hg => h2 g (List.mem_append_left _ hg))
      (fun i hi => (hc i hi).1) j hj
  · rw [solveLow_Q, solveLow_Q]
    exact flatMap_relabels_perm n n' hnn' k hkn _ _
      (fun g hg => h1 g (List.mem_append_right _ hg))
      (fun g hg => h2 g (List.mem_append_right _ hg))
      (fun i hi => (hc i hi).2) j hj

/-- The plain label leaves a graph unchanged. -/
private theorem relabelRoot_nil {n : ℕ} (Γ : Graph 3 n) : Γ.relabelRoot [] = Γ := by
  rcases Γ with ⟨comps, coeff⟩
  simp only [Graph.relabelRoot, Graph.mk.injEq, and_true]
  conv_rhs => rw [← List.map_id comps]
  refine List.map_congr_left fun c _ => ?_
  split_ifs with h
  · rcases c with ⟨kind, x, y, minor, label⟩
    obtain rfl : kind = .theta [] := h.1
    rfl
  · rfl

/-- Relabelling the `Θ` edge at `⊗` keeps the dotted blocks: it changes only the kind of a plain
`Θ` edge, which is not a dotted edge. -/
private theorem pmBlockB_relabelRoot {n : ℕ} (o : List ℕ) (Γ : Graph 3 n) :
    (Γ.relabelRoot o).pmBlockB = Γ.pmBlockB := by
  unfold Graph.pmBlockB
  congr 1
  unfold dotBlocks Graph.relabelRoot
  rw [List.foldl_map]
  congr 1
  funext P c
  by_cases h : c.kind = .theta [] ∧ (c.x = .inl 0 ∨ c.y = .inl 0)
  · simp [h]
  · simp only [h, ↓reduceIte]

/-- The graphs obtained from `g` by relabelling the `Θ` edge at `⊗` with the labels of
`chainLabels n`. -/
private def relabelsPos (n : ℕ) (g : Σ m : ℕ, Graph 3 m) : List (Σ m : ℕ, Graph 3 m) :=
  (chainLabels n).map fun o => ⟨g.1, g.2.relabelRoot o⟩

private theorem relabels_eq_cons (n : ℕ) (g : Σ m : ℕ, Graph 3 m) :
    relabels n g = g :: relabelsPos n g := by
  simp [relabels, relabelsPos, relabelRoot_nil]

/-- A relabelled copy has a label of excess `≥ 1`, so none has scaling order `≤ ord g`, and none
lies in the filter of the graphs with `⊕`, `⊖` in one dotted block when `g` does not. -/
private theorem relabelsPos_filter_nil (n : ℕ) (g : Σ m : ℕ, Graph 3 m) (hg : g.2.ThetaRooted)
    (j : ℤ) (hj : g.2.pmBlockB = true → j ≤ g.2.ord) :
    (relabelsPos n g).filter (fun h => h.2.pmBlockB && decide (h.2.ord = j)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro h hh hp
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hh
  have h1 := chainLabels_entries n o ho
  have h2 := labelInc_cast o fun e he => by have := h1 e he; omega
  have h3 := length_le_labelInc o h1
  have h5 : 0 < o.length := List.length_pos_iff.2 (chainLabelsAux_ne_nil _ _ o ho)
  simp only [Bool.and_eq_true, decide_eq_true_eq, ord_relabelRoot g.2 hg o,
    pmBlockB_relabelRoot] at hp
  have := hj hp.1
  omega

/-- The relabelled copies of scaling order `j ≤ n + ord g - 2` with `⊕`, `⊖` in one dotted block
do not depend on the order `n` of the labels. -/
private theorem relabelsPos_filter_eq (n n' : ℕ) (hn : n ≤ n') (g : Σ m : ℕ, Graph 3 m)
    (hg : g.2.ThetaRooted) (j : ℕ) (hj : (j : ℤ) ≤ n + g.2.ord - 2) :
    (relabelsPos n g).filter (fun h => h.2.pmBlockB && decide (h.2.ord = (j : ℤ))) =
      (relabelsPos n' g).filter (fun h => h.2.pmBlockB && decide (h.2.ord = (j : ℤ))) := by
  unfold relabelsPos
  rw [List.filter_map, List.filter_map]
  congr 1
  have hp : ∀ o, ((fun h : (Σ m : ℕ, Graph 3 m) => h.2.pmBlockB && decide (h.2.ord = (j : ℤ))) ∘
      fun o : List ℕ => (⟨g.1, g.2.relabelRoot o⟩ : Σ m : ℕ, Graph 3 m)) o =
        (g.2.pmBlockB && decide (g.2.ord + ((o.sum : ℤ) - 2 * o.length) = j)) := by
    intro o
    simp only [Function.comp, ord_relabelRoot g.2 hg o, pmBlockB_relabelRoot]
  rw [List.filter_congr (fun o _ => hp o), List.filter_congr (fun o _ => hp o)]
  refine chainLabels_filter n n' hn _ fun o ho hpo => ?_
  have h1 := chainLabels_entries n' o ho
  have h2 := labelInc_cast o fun e he => by have := h1 e he; omega
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpo
  omega

private theorem flatMap_cons_perm {α : Type*} (l : List α) (f : α → List α) :
    (l.flatMap fun g => g :: f g).Perm (l ++ l.flatMap f) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.cons_append]
    exact ((ih.append_left (f a)).trans (List.perm_append_comm_assoc _ _ _)).cons a

/-- The graphs with `⊕`, `⊖` in one dotted block of scaling order `j` of the solved record
`𝒬.solvePM n`: those of `R`, `A`, `Q` of `𝒬`, and the relabelled copies of the graphs of `R`, `Q`
of scaling order `≤ j - 1` with `⊕`, `⊖` in one dotted block (labels of any order `N ≥ n`). -/
private theorem solvePM_filter_perm (n N : ℕ) (hnN : n ≤ N) (𝒬 : TEqRec) (j : ℕ)
    (hj : j ≤ n + 2)
    (hRQ : ∀ g ∈ 𝒬.R ++ 𝒬.Q, g.2.ThetaRooted ∧ 2 ≤ g.2.ord ∧ (g.2.PMBlock → 4 ≤ g.2.ord))
    (hA : ∀ g ∈ 𝒬.A, ((j - 1 : ℕ) : ℤ) < g.2.ord) :
    (((𝒬.solvePM n).R ++ (𝒬.solvePM n).A ++ (𝒬.solvePM n).Q).filter
        fun g => g.2.pmBlockB && decide (g.2.ord = (j : ℤ))).Perm
      (((𝒬.R ++ 𝒬.A ++ 𝒬.Q).filter fun g => g.2.pmBlockB && decide (g.2.ord = (j : ℤ))) ++
        ((𝒬.R ++ 𝒬.A ++ 𝒬.Q).filter
            fun g => decide (g.2.ord ≤ ((j - 1 : ℕ) : ℤ)) && g.2.pmBlockB).flatMap
          fun g => (relabelsPos N g).filter
            fun h => h.2.pmBlockB && decide (h.2.ord = (j : ℤ))) := by
  set P : (Σ m : ℕ, Graph 3 m) → Bool := fun g => g.2.pmBlockB && decide (g.2.ord = (j : ℤ))
    with hP
  set Qj : (Σ m : ℕ, Graph 3 m) → Bool :=
    fun g => decide (g.2.ord ≤ ((j - 1 : ℕ) : ℤ)) && g.2.pmBlockB with hQj
  have hR : (𝒬.solvePM n).R = 𝒬.R.flatMap fun g => g :: relabelsPos n g := by
    change 𝒬.R.flatMap (relabels n) = _
    exact List.flatMap_congr fun g _ => relabels_eq_cons n g
  have hQ : (𝒬.solvePM n).Q = 𝒬.Q.flatMap fun g => g :: relabelsPos n g := by
    change 𝒬.Q.flatMap (relabels n) = _
    exact List.flatMap_congr fun g _ => relabels_eq_cons n g
  have hAe : (𝒬.solvePM n).A = 𝒬.A := rfl
  have hperm : ((𝒬.solvePM n).R ++ (𝒬.solvePM n).A ++ (𝒬.solvePM n).Q).Perm
      ((𝒬.R ++ 𝒬.A ++ 𝒬.Q) ++ (𝒬.R ++ 𝒬.Q).flatMap (relabelsPos n)) := by
    rw [hR, hQ, hAe, List.flatMap_append]
    refine (((flatMap_cons_perm 𝒬.R (relabelsPos n)).append_right _).append
      (flatMap_cons_perm 𝒬.Q (relabelsPos n))).trans ?_
    classical
    refine List.perm_iff_count.2 fun x => ?_
    simp only [List.count_append]
    omega
  refine (hperm.filter P).trans ?_
  rw [List.filter_append]
  refine List.Perm.append_left _ ?_
  rw [List.filter_flatMap]
  have hnil : ∀ g ∈ 𝒬.R ++ 𝒬.Q, Qj g = false → (relabelsPos n g).filter P = [] := by
    intro g hg hq
    refine relabelsPos_filter_nil n g (hRQ g hg).1 j fun hb => ?_
    have h2 := (hRQ g hg).2.1
    simp only [hQj, hb, Bool.and_true, decide_eq_false_iff_not, not_le] at hq
    omega
  rw [flatMap_eq_flatMap_filter _ Qj _ hnil]
  have hfil : (𝒬.R ++ 𝒬.Q).filter Qj = (𝒬.R ++ 𝒬.A ++ 𝒬.Q).filter Qj := by
    have hAn : 𝒬.A.filter Qj = [] := by
      refine List.filter_eq_nil_iff.2 fun g hg hq => ?_
      have := hA g hg
      simp only [hQj, Bool.and_eq_true, decide_eq_true_eq] at hq
      omega
    simp only [List.filter_append, hAn, List.append_nil]
  rw [hfil]
  refine List.Perm.of_eq (List.flatMap_congr fun g hg => ?_)
  have hg' := (List.mem_filter.1 hg)
  have hmem : g ∈ 𝒬.R ++ 𝒬.Q := by
    rcases List.mem_append.1 hg'.1 with h | h
    · rcases List.mem_append.1 h with h | h
      · exact List.mem_append_left _ h
      · have := hA g h
        simp only [hQj, Bool.and_eq_true, decide_eq_true_eq] at hg'
        omega
    · exact List.mem_append_right _ h
  have h4 : 4 ≤ g.2.ord := by
    simp only [hQj, Bool.and_eq_true] at hg'
    exact (hRQ g hmem).2.2 hg'.2.2
  exact relabelsPos_filter_eq n N hnN g (hRQ g hmem).1 j (by omega)

/-- The graphs of order `≤ k` of `R` and `Q` of the solved `T`-equation ([II, (6.1)–(6.3)]) do not
depend on the order `n ≥ k` of the solution: if the graphs of `R` and `Q` of two `T`-equations have
the form [II, Def 3.3 (4)] and order `≥ 2`, and the two agree up to order `k` ([II, Def 3.2 (7)]),
then so do their solutions of orders `n, n' ≥ k`. -/
theorem solveLow_coherent :
  ∀ (k n n' : ℕ) (𝒬 𝒬' : TEqRec), k ≤ n → k ≤ n' →
    (∀ g ∈ 𝒬.R ++ 𝒬.Q, g.2.ThetaRooted ∧ 2 ≤ g.2.ord) →
    (∀ g ∈ 𝒬'.R ++ 𝒬'.Q, g.2.ThetaRooted ∧ 2 ≤ g.2.ord) →
    TRec.Coherent k 𝒬.toTRec 𝒬'.toTRec → TRec.Coherent k (𝒬.solveLow n) (𝒬'.solveLow n') := by
  intro k n n' 𝒬 𝒬' hkn hkn' h1 h2 hc
  rcases le_total n n' with h | h
  · exact solveLow_coherent_le k n n' 𝒬 𝒬' hkn h h1 h2 hc
  · exact coherent_symm (solveLow_coherent_le k n' n 𝒬' 𝒬 hkn' h h2 h1 (coherent_symm hc))

/-- Solving keeps `TRec.CoherentPM` ([II, (6.1)–(6.3)], [II, (6.9)]): for `T`-equations whose
graphs of `R`, `Q` have the form [II, Def 3.3 (4)], scaling order `≥ 2`, and order `≥ 4` when
`⊕`, `⊖` lie in one dotted block ([II, Def 6.3]), and whose graphs of `A` have order `> n₁` resp.
`> n₂`, the coherence up to `m ≤ min(n₁, n₂) + 1` passes to the solved records
`TEqRec.solvePM n₁`, `TEqRec.solvePM n₂`. -/
theorem solvePM_coherentPM :
  ∀ (m n₁ n₂ : ℕ) (𝒬 𝒬' : TEqRec), m ≤ n₁ + 1 → m ≤ n₂ + 1 →
    (∀ g ∈ 𝒬.R ++ 𝒬.Q, g.2.ThetaRooted ∧ 2 ≤ g.2.ord ∧ (g.2.PMBlock → 4 ≤ g.2.ord)) →
    (∀ g ∈ 𝒬'.R ++ 𝒬'.Q, g.2.ThetaRooted ∧ 2 ≤ g.2.ord ∧ (g.2.PMBlock → 4 ≤ g.2.ord)) →
    (∀ g ∈ 𝒬.A, (n₁ : ℤ) < g.2.ord) → (∀ g ∈ 𝒬'.A, (n₂ : ℤ) < g.2.ord) →
    TRec.CoherentPM m 𝒬.toTRec 𝒬'.toTRec → TRec.CoherentPM m (𝒬.solvePM n₁) (𝒬'.solvePM n₂) := by
  intro m n₁ n₂ 𝒬 𝒬' hm₁ hm₂ h₁ h₂ hA₁ hA₂ hc j hj
  have e₁ := solvePM_filter_perm n₁ (n₁ + n₂) (by omega) 𝒬 j (by omega) h₁
    fun g hg => by have := hA₁ g hg; omega
  have e₂ := solvePM_filter_perm n₂ (n₁ + n₂) (by omega) 𝒬' j (by omega) h₂
    fun g hg => by have := hA₂ g hg; omega
  refine e₁.trans (List.Perm.trans ?_ e₂.symm)
  refine List.Perm.append (hc j hj) (List.Perm.flatMap_right _ ?_)
  have hpos : ∀ g ∈ ((𝒬.R ++ 𝒬.A ++ 𝒬.Q).filter fun g => g.2.pmBlockB) ++
      ((𝒬'.R ++ 𝒬'.A ++ 𝒬'.Q).filter fun g => g.2.pmBlockB), 0 < g.2.ord := by
    intro g hg
    simp only [List.mem_append, List.mem_filter] at hg
    rcases hg with ⟨(⟨h | h⟩ | h), -⟩ | ⟨(⟨h | h⟩ | h), -⟩
    · have := (h₁ g (List.mem_append_left _ h)).2.1; omega
    · have := hA₁ g h; omega
    · have := (h₁ g (List.mem_append_right _ h)).2.1; omega
    · have := (h₂ g (List.mem_append_left _ h)).2.1; omega
    · have := hA₂ g h; omega
    · have := (h₂ g (List.mem_append_right _ h)).2.1; omega
  have key := perm_filter_le (fun g : Σ m : ℕ, Graph 3 m => g.2.ord) _ _ hpos (j - 1)
    fun i hi => by
      rw [List.filter_filter, List.filter_filter]
      have hf : ∀ l : List (Σ m : ℕ, Graph 3 m),
          l.filter (fun g => decide (g.2.ord = (i : ℤ)) && g.2.pmBlockB) =
            l.filter (fun g => g.2.pmBlockB && decide (g.2.ord = (i : ℤ))) :=
        fun l => List.filter_congr fun g _ => Bool.and_comm _ _
      rw [hf, hf]
      exact hc i (by omega)
  rw [List.filter_filter, List.filter_filter] at key
  exact key

private theorem coherentPM_symm {m : ℕ} {a b : TRec} (h : TRec.CoherentPM m a b) :
    TRec.CoherentPM m b a :=
  fun j hj => (h j hj).symm

private theorem coherentPM_trans {m : ℕ} {a b c : TRec} (h₁ : TRec.CoherentPM m a b)
    (h₂ : TRec.CoherentPM m b c) : TRec.CoherentPM m a c :=
  fun j hj => (h₁ j hj).trans (h₂ j hj)

private theorem coherentPM_mono {m m' : ℕ} {a b : TRec} (h : TRec.CoherentPM m' a b)
    (hm : m ≤ m') : TRec.CoherentPM m a b :=
  fun j hj => h j (hj.trans hm)

private theorem coherent_trans {k : ℕ} {a b c : TRec} (h₁ : TRec.Coherent k a b)
    (h₂ : TRec.Coherent k b c) : TRec.Coherent k a c :=
  fun j hj => ⟨(h₁ j hj).1.trans (h₂ j hj).1, (h₁ j hj).2.trans (h₂ j hj).2⟩

private theorem coherent_mono {k k' : ℕ} {a b : TRec} (h : TRec.Coherent k' a b) (hk : k ≤ k') :
    TRec.Coherent k a b :=
  fun j hj => h j (hj.trans hk)

/-- The graphs of `R` and `Q` of a `T`-equation have the form [II, Def 3.3 (4)] and order `≥ 2`. -/
private theorem rooted_of_struct {Sig : ℕ → Expansion 2} {n D : ℕ} {𝒬 : TEqRec}
    (h : 𝒬.IsTEqStruct Sig n D) : ∀ g ∈ 𝒬.R ++ 𝒬.Q, g.2.ThetaRooted ∧ 2 ≤ g.2.ord := by
  obtain ⟨-, -, -, -, ⟨-, hR, -, hQ, -⟩, hroot, -⟩ := h
  intro g hg
  rcases List.mem_append.1 hg with hg | hg
  · exact ⟨hroot g (by simp [hg]), by have := (hR g hg).2.2.1; omega⟩
  · exact ⟨hroot g (by simp [hg]), (hQ g hg).2⟩

/-- The graphs of `R` and `Q` of a `T`-equation have the form [II, Def 3.3 (4)], order `≥ 2`,
and order `≥ 4` when `⊕`, `⊖` lie in one dotted block. -/
private theorem pmRooted_of_struct {Sig : ℕ → Expansion 2} {n D : ℕ} {𝒬 : TEqRec}
    (h : 𝒬.IsTEqStruct Sig n D) :
    ∀ g ∈ 𝒬.R ++ 𝒬.Q, g.2.ThetaRooted ∧ 2 ≤ g.2.ord ∧ (g.2.PMBlock → 4 ≤ g.2.ord) := by
  have hr := rooted_of_struct h
  obtain ⟨-, -, -, -, -, -, ⟨-, -, -, hRA, hQ, -⟩⟩ := h
  intro g hg
  refine ⟨(hr g hg).1, (hr g hg).2, fun hp => ?_⟩
  rcases List.mem_append.1 hg with hg | hg
  · have := hRA g (List.mem_append_left _ hg) hp; omega
  · exact hQ g hg hp

/-- The graphs of `A` of an `n`-th order `T`-equation have scaling order `> n`. -/
private theorem aOrd_of_struct {Sig : ℕ → Expansion 2} {n D : ℕ} {𝒬 : TEqRec}
    (h : 𝒬.IsTEqStruct Sig n D) : ∀ g ∈ 𝒬.A, (n : ℤ) < g.2.ord := by
  obtain ⟨-, -, -, -, ⟨-, -, hA, -⟩, -⟩ := h
  exact fun g hg => (hA g hg).2

/-- The induction step `H(n - 1) ⇒ H(n)` ([II, Theorem 3.7, Corollary 3.8, Lemma 3.9]) from the
`T`-equation (`tEquationStmt`), the self-energy property of `Σ_n` (`selfEnergyStepStmt`) and
the solution of the `T`-equation (`solveStmt`), for the construction `Strat` of `tEquationStmt`.
The families of `H(n)` are those of `H(n - 1)` with the order-`n` records added; the `T`-equation
of order `n` is `Strat n D` applied to the `T`-expansion of order `n - 1`. -/
theorem inductionStep_of_parts (d : ℕ) (Svar : VarFamily d) (hT : tEquationStmt)
    (hS : selfEnergyStepStmt d Svar) (hV : solveStmt d Svar) :
    ∃ Strat : ℕ → ℕ → TRec → TEqRec, inductionStepStmt d Svar Strat := by
  obtain ⟨Strat, hT⟩ := hT
  refine ⟨Strat, fun n hn Sig hH => ?_⟩
  obtain ⟨hSE, 𝒬, 𝒯, hfam⟩ := hH
  obtain ⟨E, hTn⟩ := hT n hn Sig 𝒬 𝒯 hfam
  let 𝒬n : ℕ → TEqRec := fun D => Strat n D (𝒯 (n - 1) D)
  have hTE : ∀ D, n < D → (𝒬n D).SigN = E ∧ IsTEquation d Svar Sig n D (𝒬n D) :=
    fun D hD => ⟨(hTn D hD).1, hSE, (hTn D hD).2.1⟩
  have hSn := hS Strat n hn Sig E 𝒬n ⟨hSE, 𝒬, 𝒯, hfam⟩ hTE
  obtain ⟨𝒯n, hsol⟩ :=
    hV n hn Sig E 𝒬n hTE (fun D D' hD hDD' => (hTn D hD).2.2.2.2 D' hDD') hSn
  have hagree : ∀ k ≤ n - 1, Function.update Sig n E k = Sig k :=
    fun k hk => Function.update_of_ne (by omega) _ _
  have hSE' := ((hWith_congr d Svar Strat Sig (Function.update Sig n E) (n - 1) hagree).mp
    ⟨hSE, 𝒬, 𝒯, hfam⟩).1
  have hfam' := hFam_congr Strat Sig (Function.update Sig n E) (n - 1) 𝒬 𝒯 hagree hfam
  refine ⟨E, fun k hk4 hkn hev => ?_, fun k D => if k = n then 𝒬n D else 𝒬 k D,
    fun k D => if k = n then 𝒯n D else 𝒯 k D, fun k D hk2 hkn hkD => ?_,
    fun k D hk3 hkn hkD => ?_, fun k k' D hk2 hkk' hk'n hk'D => ?_,
    fun k D D' hk2 hkn hkD hDD' => ?_, fun D hn2 hD => ?_, fun k D hk3 hkn hkD => ?_⟩
  · by_cases h : k = n
    · exact h ▸ hSn
    · exact hSE' k hk4 (by omega) hev
  · by_cases h : k = n
    · subst h
      simp only [↓reduceIte]
      exact ⟨isTEqStruct_congr Sig _ _ D (𝒬n D) (fun j hj => Function.update_of_ne (by omega) _ _)
        (hTn D hkD).2.1, (hsol D hkD).1.2, (hsol D hkD).2.1, (hsol D hkD).2.2.1⟩
    · simp only [h, ↓reduceIte]
      exact hfam'.1 k D hk2 (by omega) hkD
  · by_cases h : k = n
    · subst h
      simp only [↓reduceIte, Function.update_self]
      exact (hTn D hkD).1
    · simp only [h, ↓reduceIte]
      exact hfam'.2.1 k D hk3 (by omega) hkD
  · by_cases h' : k' = n
    · subst h'
      by_cases h : k = k'
      · subst h
        simp only [↓reduceIte]
        exact ⟨fun j _ => ⟨List.Perm.refl _, List.Perm.refl _⟩,
          fun j _ => ⟨List.Perm.refl _, List.Perm.refl _⟩, fun j _ => List.Perm.refl _⟩
      · simp only [h, ↓reduceIte]
        have hk1 : k ≤ k' - 1 := by omega
        have hc := hfam.2.2.1 k (k' - 1) D hk2 hk1 le_rfl (by omega)
        have hst := hfam.1 k D hk2 (by omega) (by omega)
        have hq : TRec.Coherent k (𝒬 k D).toTRec (𝒬n D).toTRec :=
          coherent_trans hc.1 (coherent_mono (hTn D hk'D).2.2.1 hk1)
        have hst' := hfam.1 (k' - 1) D (by omega) le_rfl (by omega)
        have hmid : TRec.CoherentPM k' ((𝒬 (k' - 1) D).solvePM (k' - 1)) ((𝒬n D).solvePM k') :=
          solvePM_coherentPM k' (k' - 1) k' (𝒬 (k' - 1) D) (𝒬n D) (by omega) (by omega)
            (pmRooted_of_struct hst'.1) (pmRooted_of_struct (hTn D hk'D).2.1)
            (by have := aOrd_of_struct hst'.1; exact this)
            (aOrd_of_struct (hTn D hk'D).2.1) (hTn D hk'D).2.2.2.1
        have hchain : TRec.CoherentPM k' (𝒯 (k' - 1) D) (𝒯n D) :=
          coherentPM_trans (coherentPM_mono hst'.2.2.2 (by omega))
            (coherentPM_trans hmid (coherentPM_symm (coherentPM_mono (hsol D hk'D).2.2.1
              (by omega))))
        refine ⟨hq, coherent_trans (coherent_symm hst.2.2.1)
          (coherent_trans ?_ (coherent_mono (hsol D hk'D).2.1 hkk')),
          coherentPM_trans hc.2.2 (coherentPM_mono hchain (by omega))⟩
        exact solveLow_coherent k k k' (𝒬 k D) (𝒬n D) le_rfl hkk' (rooted_of_struct hst.1)
          (rooted_of_struct (hTn D hk'D).2.1) hq
    · have h : k ≠ n := by omega
      simp only [h', h, ↓reduceIte]
      exact hfam'.2.2.1 k k' D hk2 hkk' (by omega) hk'D
  · by_cases h : k = n
    · subst h
      simp only [↓reduceIte]
      exact ⟨(hTn D hkD).2.2.2.2 D' hDD', (hsol D hkD).2.2.2 D' hDD'⟩
    · simp only [h, ↓reduceIte]
      exact hfam'.2.2.2.1 k D D' hk2 (by omega) hkD hDD'
  · have h : (2 : ℕ) ≠ n := by omega
    simp only [h, ↓reduceIte]
    exact hfam.2.2.2.2.1 D (by omega) hD
  · have h1 : k - 1 ≠ n := by omega
    by_cases h : k = n
    · subst h
      simp only [h1, ↓reduceIte]
      rfl
    · simp only [h, h1, ↓reduceIte]
      exact hfam.2.2.2.2.2 k D hk3 (by omega) hkD



section Instances

instance instDecLabelFreeC {k n : ℕ} (Γ : Graph k n) : Decidable Γ.LabelFree :=
  inferInstanceAs (Decidable (∀ c ∈ Γ.comps, c.label = none))

instance instDecIsQGraphC {k n : ℕ} (Γ : Graph k n) : Decidable Γ.IsQGraph :=
  inferInstanceAs (Decidable (∃ u : Atom k n, (∃ c ∈ Γ.comps, c.label = some (.Q, u)) ∧
    ∀ c ∈ Γ.comps, (c.kind.isRandom = true ∨ c.label.isSome = true) → c.label = some (.Q, u)))

end Instances

end RBM8D.Graphs
