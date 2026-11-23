module

public import RBM8D.Prob.PartialPoly
public import RBM8D.Graph.Local.Model

@[expose] public section

/-!
# The Gaussian instance of the model relations

`modelAdm_gauss`: the model of [I, Assumption 1.1] satisfies `ModelAdm` for every real symmetric `S ≥ 0` with row sums `1` and every `z` with `Im z > 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal BigOperators

universe u v w

namespace RBM8D.Graphs

/-- The model relations `ModelAdm` hold for the Gaussian model of [I, Assumption 1.1]: `E` is the
Gaussian integral, `Meas x` the functions free of row `x` ([I, §1.4]), `Good` the functions of
polynomial growth, `Test` the test functions and `dh` the Wirtinger derivatives; the integration
by parts is [I, Lemma 2.4], and the data fields `S⁺`, `Θ` are [I, (2.1), (1.16)]. -/
theorem modelAdm_gauss (ι : Type) [Fintype ι] [DecidableEq ι] :
    modelAdm_gaussStmt ι (Sample ι) hmat Pexp := by
  intro S z hS hnn hrow hz
  have hz0 : z.im ≠ 0 := hz.ne'
  have hlaws := pqLaws_Pexp_poly S hS hnn
  have hG : ∀ ω, (modelData S z hmat ω).Gm ∅ = green (hmat ω) z := by
    intro ω
    have h : ¬ ∃ x : ι, (∅ : Finset ι) = {x} := by
      rintro ⟨x, hx⟩
      exact Finset.singleton_ne_empty x hx.symm
    simp only [modelData, dite_eq_right h]
  have hMin : ∀ ω x,
      (modelData S z hmat ω).Gm {x} = Matrix.of (greenMinor (green (hmat ω) z) x) := by
    intro ω x
    have h : ∃ y : ι, ({x} : Finset ι) = {y} := ⟨x, rfl⟩
    simp only [modelData, dite_eq_left h]
    rw [← Finset.singleton_inj.mp h.choose_spec]
  refine ⟨{
    H := hmat
    z := z
    S := S
    E := fun F => ∫ ω, F ω ∂(gaussLaw S)
    Meas := fun x => FreeOf (rowCoords x)
    Good := PolyMeas
    Test := TestFn
    dh := dh
    isHermitian := hmat_isHermitian
    im_pos := hz
    isSymm := hS
    nonneg := hnn
    rowSum := hrow
    data_m := fun _ => rfl
    data_G := hG
    data_minor := hMin
    data_S := fun _ => rfl
    data_Sp := fun ω => modelData_Sp S z hmat ω hnn hrow hz
    data_Sm := fun _ => rfl
    data_Theta := fun ω => modelData_Theta S z hmat ω hnn hrow hz
    laws := pqLaws_toLaws hlaws fun x a => (freeOf_closed (rowCoords x)).1 a
    meas_add := fun x => (freeOf_closed (rowCoords x)).2.1
    meas_mul := fun x => (freeOf_closed (rowCoords x)).2.2
    meas_minor := ?_
    P_star := fun x F _ => partialExp_star S (rowCoords x) F
    good_star := hlaws.adm_conj
    good_entry := ?_
    good_inv := ?_
    good_H := polyMeas_hmat
    test_good := polyMeas_of_testFn
    test_const := testFn_closed.1
    test_add := testFn_closed.2.1
    test_mul := testFn_closed.2.2.1
    test_star := testFn_closed.2.2.2.1
    test_entry := ?_
    test_dh := testFn_closed.2.2.2.2.1
    dh_add := dh_add
    dh_mul := dh_mul
    dh_const := dh_const
    dh_green := fun a b x y => funext (dh_green z hz0 a b x y)
    dh_conj_green := fun a b x y => funext (dh_conj_green z hz0 a b x y)
    ibp := fun x a b hab F hF =>
      funext (partialExp_hmat_mul S hS hnn (rowCoords x) a b
        (entryCoords_subset_rowCoords x a b hab) F hF) }⟩
  · intro x a b
    simp only [hMin, Matrix.of_apply]
    exact freeOf_greenMinor z hz x a b
  · intro T a b
    by_cases h : ∃ x, T = {x}
    · obtain ⟨x, rfl⟩ := h
      simp only [hMin, Matrix.of_apply]
      exact polyMeas_greenMinor z hz x a b
    · simp only [modelData, dite_eq_right h]
      exact polyMeas_of_testFn _ (testFn_green z hz0 a b)
  · intro a
    simp only [hG]
    exact polyMeas_inv_green_diag z hz a
  · intro a b
    simp only [hG]
    exact testFn_green z hz0 a b

section Instance

end Instance

end RBM8D.Graphs
