module

public import RBM8D.MainDefs
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# The torus `Z_L^d` and its periodic distance

The paper works on the torus `Z_L^d` with the periodic `ℓ^∞` distance `‖x - y‖_L`
([I, (1.2)–(1.3)]).  `zdist L u` is the distance `|[u]_L|` from `u` to `0` on the cycle `ZMod L`,
where `[u]_L` is the representative of `u` in `(-L/2, L/2]` (`ZMod.valMinAbs`), and `zdistInf`
is the periodic `ℓ^∞` distance to the origin on `Zd d L`.
-/

namespace RBM8D

theorem zdist_eq_zero_iff (L : ℕ) [NeZero L] {u : ZMod L} : zdist L u = 0 ↔ u = 0 := by
  have hu : u.val < L := ZMod.val_lt u
  constructor
  · intro h
    have : u.val = 0 := by simp only [zdist] at h; omega
    exact (ZMod.val_eq_zero u).mp this
  · rintro rfl; simp [zdist]

theorem zdist_add_le (L : ℕ) [NeZero L] (u v : ZMod L) :
    zdist L (u + v) ≤ zdist L u + zdist L v := by
  have hu : u.val < L := ZMod.val_lt u
  have hv : v.val < L := ZMod.val_lt v
  have hadd : (u + v).val = (u.val + v.val) % L := ZMod.val_add u v
  rcases lt_or_ge (u.val + v.val) L with h | h
  · rw [Nat.mod_eq_of_lt h] at hadd
    simp only [zdist, hadd]
    omega
  · have hmod : (u.val + v.val) % L = u.val + v.val - L := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [hmod] at hadd
    simp only [zdist, hadd]
    omega

theorem zdist_neg (L : ℕ) [NeZero L] (u : ZMod L) : zdist L (-u) = zdist L u := by
  by_cases h : u = 0
  · simp [h]
  · have hu : u.val < L := ZMod.val_lt u
    have hval : (-u).val = L - u.val := by simp [ZMod.neg_val, h]
    simp only [zdist, hval]
    omega

/-- `zdist L u` is the absolute value of the representative `[u]_L` of `u` in `(-L/2, L/2]`. -/
theorem zdist_eq_natAbs_valMinAbs (L : ℕ) [NeZero L] (u : ZMod L) :
    zdist L u = u.valMinAbs.natAbs := by
  rw [ZMod.valMinAbs_natAbs_eq_min]
  rfl

/-- The distance to the origin on the cycle `ZMod L` is at most `L / 2`. -/
theorem zdist_le_half (L : ℕ) [NeZero L] (u : ZMod L) : zdist L u ≤ L / 2 := by
  have hu : u.val < L := ZMod.val_lt u
  simp only [zdist]
  omega

/-- The torus `Z_L^d` has `L ^ d` points. -/
theorem card_Zd (d L : ℕ) [NeZero L] : Fintype.card (Zd d L) = L ^ d := by
  simp [Zd, ZMod.card]

theorem zdist_le_zdistInf (d L : ℕ) (x : Zd d L) (i : Fin d) :
    zdist L (x i) ≤ zdistInf d L x :=
  Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i)

theorem zdistInf_eq_zero_iff (d L : ℕ) [NeZero L] {x : Zd d L} :
    zdistInf d L x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have h1 : zdist L (x i) = 0 := Nat.le_zero.mp (h ▸ zdist_le_zdistInf d L x i)
    simpa using (zdist_eq_zero_iff L).mp h1
  · rintro rfl
    simp [zdistInf, zdist]

theorem zdistInf_add_le (d L : ℕ) [NeZero L] (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y :=
  Finset.sup_le fun i _ =>
    (zdist_add_le L (x i) (y i)).trans
      (Nat.add_le_add (zdist_le_zdistInf d L x i) (zdist_le_zdistInf d L y i))

theorem zdistInf_neg (d L : ℕ) [NeZero L] (x : Zd d L) :
    zdistInf d L (-x) = zdistInf d L x := by
  simp only [zdistInf, Pi.neg_apply, zdist_neg]

theorem zdistInf_le_half (d L : ℕ) [NeZero L] (x : Zd d L) : zdistInf d L x ≤ L / 2 :=
  Finset.sup_le fun i _ => zdist_le_half L (x i)

end RBM8D
