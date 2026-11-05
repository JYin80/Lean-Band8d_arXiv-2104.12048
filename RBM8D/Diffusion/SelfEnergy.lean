import RBM8D.Diffusion.Defs
import RBM8D.TExp.Closure
import RBM8D.SelfEnergy.Contract

/-!
# The self-energies `Σ_l` of [I, Theorem 1.5]

One family `Sig` of formal sums with `H(n)` for every `n ≥ 2` (the hypothesis `jointHStmt`) gives
the family of matrices `Σ_l(W, L, z)` of `SigmaOf` ([I, Def 2.13 (i)], [I, (1.25)]); this is
`selfEnergyFamilyStmt`.

* The shape of `Sig l` for `l ≥ 4` is read from the `T`-equation of order `l` in `H(l)`: its `Σ_l`
  is `Sig l` and has the shape of an `l`-th order self-energy ([II, Def 3.3]).
* `Σ_l(W, L, z)` is the value `sigMat Sig (S_{W,L}) z l` wherever `S_{W,L}` is symmetric, and `0`
  elsewhere. `S_{W,L}` is translation invariant for every `(W, L)`; where it is also symmetric,
  the matrices `sigUpTo Sig S z N k` and `sigMat Sig S z l` are invariant under translations and
  under the reflection `x ↦ -x` for every `z`, which is [I, (1.25)].
-/

noncomputable section

namespace RBM8D

open Graphs

/-! ## Invariance of the self-energy matrices -/

/-- A kernel on `Z_L^d` invariant under translations and under the reflection `x ↦ -x`. -/
private abbrev Inv2 {d L : ℕ} (M : Matrix (Zd d L) (Zd d L) ℂ) : Prop :=
  TransInv M ∧ ∀ x y, M (-x) (-y) = M x y

/-- The self-energy matrices of `Sig` below order `N` on a symmetric translation invariant
variance matrix `S` are invariant under translations and under the reflection, for every `z`. -/
private theorem inv2_sigUpTo {d L : ℕ} [NeZero L] (Sig : ℕ → Expansion 2)
    (S : Matrix (Zd d L) (Zd d L) ℝ) (hT : TransInv S) (hs : ∀ x y, S x y = S y x) (z : ℂ) :
    ∀ N k, Inv2 (sigUpTo Sig S z N k) := by
  intro N
  induction N with
  | zero => intro k; exact ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
  | succ N ih =>
    intro k
    simp only [sigUpTo]
    by_cases hk : k = N
    · subst hk
      rw [Function.update_self]
      exact symKer_val S hT hs z _ ih (Sig k)
    · rw [Function.update_of_ne hk]
      exact ih k

/-- `Σ_l` is invariant under translations and under the reflection, for every `z`. -/
private theorem inv2_sigMat {d L : ℕ} [NeZero L] (Sig : ℕ → Expansion 2)
    (S : Matrix (Zd d L) (Zd d L) ℝ) (hT : TransInv S) (hs : ∀ x y, S x y = S y x) (z : ℂ)
    (l : ℕ) : Inv2 (sigMat Sig S z l) :=
  symKer_val S hT hs z _ (inv2_sigUpTo Sig S hT hs z l) (Sig l)

/-- The identities of [I, (1.25)] for a kernel invariant under translations and the reflection. -/
private theorem inv2_id {d L : ℕ} (K : Matrix (Zd d L) (Zd d L) ℂ) (h : Inv2 K)
    (x a : Zd d L) : K x (x + a) = K 0 a ∧ K 0 a = K 0 (-a) := by
  refine ⟨?_, ?_⟩
  · have := h.1 0 a x
    rw [zero_add, add_comm a x] at this
    exact this
  · have := h.2 0 (-a)
    rw [neg_zero, neg_neg] at this
    exact this

/-! ## The witness `Σ_l(W, L, z)` -/

open Classical in
/-- The matrices `Σ_l(W, L, z)`: the value of `Sig l` on the deterministic record of `S_{W,L}`
where `S_{W,L}` is symmetric, and `0` elsewhere. -/
private def selfEnergyWitness (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2) : SigmaFam d :=
  fun l W L _ z =>
    if (Smat P.ψ W L).IsSymm then sigMat Sig (Smat P.ψ W L) z l else 0

/-- `SigmaOf` for a family `Sig` all of whose orders `l ≥ 4` have the shape of a self-energy:
the matrices of `selfEnergyWitness` satisfy the value clause on the symmetric region and
[I, (1.25)] at every `(W, L, z)`. -/
theorem selfEnergy_sigmaOf_of_shape (d : ℕ) (P : Profile d) (Sig : ℕ → Expansion 2)
    (hshape : ∀ l, 4 ≤ l → SelfEnergyShape l (Sig l)) :
    ∃ Sg : SigmaFam d, SigmaOf d P Sig Sg := by
  refine ⟨selfEnergyWitness d P Sig, hshape, fun l _ W L _ z hsymm => ?_,
    fun l _ W L _ z x a => ?_⟩
  · simp only [selfEnergyWitness, hsymm, ↓reduceIte]
  · by_cases hsymm : (Smat P.ψ W L).IsSymm
    · simp only [selfEnergyWitness, hsymm, ↓reduceIte]
      exact inv2_id _ (inv2_sigMat Sig _ (Smat_transInv _ L P.ψ W)
        (fun x y => hsymm.apply y x) z l) x a
    · simp only [selfEnergyWitness, hsymm, ↓reduceIte]
      simp

/-! ## The family of self-energies -/

/-- **[I, Theorem 1.5] (the self-energies), [I, Def 2.13 (i)], [I, (1.25)]**: from one family `Sig`
with `H(n)` for every `n ≥ 2` for the variance family `smatVar P`, the same family has the shape
of a self-energy at every order `l ≥ 4`, and there are matrices `Σ_l(W, L, z)` with `SigmaOf`. -/
theorem selfEnergyFamily : selfEnergyFamilyStmt := by
  intro d P Strat hJ
  obtain ⟨Sig, hSig⟩ := hJ
  refine ⟨Sig, hSig, selfEnergy_sigmaOf_of_shape d P Sig fun l hl => ?_⟩
  obtain ⟨𝒬, 𝒯, hF⟩ := (hSig l (by omega)).2
  have h1 := (hF.1 l (l + 1) (by omega) le_rfl (by omega)).1.2.2.2.1
  have h2 := hF.2.1 l (l + 1) (by omega) le_rfl (by omega)
  rwa [h2] at h1

end RBM8D
