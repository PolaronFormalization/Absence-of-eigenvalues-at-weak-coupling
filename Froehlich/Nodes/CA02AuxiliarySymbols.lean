import Froehlich.Nodes.CA02ScalarRegularity
import Froehlich.Nodes.RS01FreeInverse

set_option autoImplicit false

/-! Concrete derivative symbols for the existing source auxiliary weight.
The zero-order symbol is the literal already-constructed physical G.
The low-sector value one has zero derivatives of every positive order. -/
noncomputable section
open MeasureTheory
namespace Froehlich

def auxiliaryInverseWeightJet (is : List (Fin 3)) (n : ℕ) (e : ℝ) (p : GW.Space)
    (m : ℕ) (K : GW.Fock.Coordinates m) : ℝ :=
  if n ≤ m then evalScalarTerms (scalarDerivativeTerms is) ((m : ℝ)+1-(n : ℝ)-e)
    (fun i => (totalMomentum m K+p) i) else if is = [] then 1 else 0

theorem auxiliaryWeight_eq_scalar_root (n m : ℕ) (e : ℝ) (p : GW.Space)
    (hnm : n ≤ m) (K : GW.Fock.Coordinates m) :
    auxiliaryWeight n e p m K = scalarWeightRoot ((m : ℝ)+1-(n : ℝ)-e)
      (fun i => (totalMomentum m K+p) i) := by
  rw [auxiliaryWeight_of_ge n m e p hnm,scalarWeightRoot,scalarWeightSquare_euclidean]
  simp only [freeSymbol,sub_neg_eq_add]
  congr 1
  ring

theorem auxiliaryScalarParameter_ge_one (n m : ℕ) (e : ℝ) (he : e ≤ 0) (hnm : n ≤ m) :
    1 ≤ (m : ℝ)+1-(n : ℝ)-e := by
  have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  linarith

theorem auxiliaryInverseWeightJet_nil (n m : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (K : GW.Fock.Coordinates m) :
    auxiliaryInverseWeightJet [] n e p m K = (auxiliaryWeight n e p m K)⁻¹ := by
  by_cases hnm : n ≤ m
  · have hb := auxiliaryScalarParameter_ge_one n m e he hnm
    have h := congrFun (scalarDerivativeTerms_expansion ([] : List (Fin 3))
      ((m : ℝ)+1-(n : ℝ)-e) hb) (fun i => (totalMomentum m K+p) i)
    change scalarInverseRootWeight _ _ = evalScalarTerms (scalarDerivativeTerms []) _ _ at h
    rw [auxiliaryInverseWeightJet,if_pos hnm,← h,auxiliaryWeight_eq_scalar_root n m e p hnm]
    exact one_div _
  · simp only [auxiliaryInverseWeightJet,if_neg hnm,auxiliaryWeight,inv_one,ite_true]

theorem auxiliaryPhysicalFreeInverse_jet_ae (n m : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (f : HighSectorSpace n) :
    (fun K => (auxiliaryInverseWeightJet [] n e p m K : ℂ) • physicalSector m ((f : GW.Fock.Carrier) m) K)
      =ᵐ[GW.Fock.sectorMeasure m]
      physicalSector m ((auxiliaryPhysicalFreeInverse n e p he f : GW.Fock.Carrier) m) := by
  simpa only [auxiliaryInverseWeightJet_nil n m e p he] using auxiliaryPhysicalFreeInverse_ae n m e p he f

theorem auxiliaryInverseWeightJet_relative_bound (is : List (Fin 3)) (n m : ℕ)
    (e : ℝ) (p : GW.Space) (he : e ≤ 0) (K : GW.Fock.Coordinates m) :
    |auxiliaryInverseWeightJet is n e p m K| ≤
      scalarDerivativeCoefficientBound is.length * (auxiliaryWeight n e p m K)⁻¹ := by
  by_cases hnm : n ≤ m
  · have hb := auxiliaryScalarParameter_ge_one n m e he hnm
    have h := scalarDerivativeTerms_relative_bound is ((m : ℝ)+1-(n : ℝ)-e) hb
      (fun i => (totalMomentum m K+p) i)
    rw [scalarDerivativeTerms_expansion is _ hb] at h
    simpa only [auxiliaryInverseWeightJet,if_pos hnm,scalarInverseRootWeight,one_div,
      auxiliaryWeight_eq_scalar_root n m e p hnm] using h
  · by_cases his : is = []
    · subst is
      simp only [auxiliaryInverseWeightJet,if_neg hnm,auxiliaryWeight,ite_true,
        scalarDerivativeCoefficientBound,List.length_nil,abs_one,inv_one,mul_one,le_rfl]
    · simpa only [auxiliaryInverseWeightJet,if_neg hnm,if_neg his,auxiliaryWeight,if_neg hnm,abs_zero,inv_one,mul_one]
        using scalarDerivativeCoefficientBound_nonnegative is.length

theorem auxiliaryInverseWeightJet_bound (is : List (Fin 3)) (n m : ℕ)
    (e : ℝ) (p : GW.Space) (he : e ≤ 0) (K : GW.Fock.Coordinates m) :
    |auxiliaryInverseWeightJet is n e p m K| ≤ scalarDerivativeCoefficientBound is.length := by
  have hr := auxiliaryInverseWeightJet_relative_bound is n m e p he K
  have hW := auxiliaryWeight_ge_one n m e p he K
  have hi : (auxiliaryWeight n e p m K)⁻¹ ≤ 1 := by
    simpa only [one_div] using (div_le_one (zero_lt_one.trans_le hW)).mpr hW
  exact hr.trans (by nlinarith [scalarDerivativeCoefficientBound_nonnegative is.length])

theorem scalarWeightTerm_measurable {d : ℕ} (c : ℝ) (beta : Fin d → ℕ) (j : ℕ) (b : ℝ) :
    Measurable (scalarWeightTerm c beta j b) := by
  unfold scalarWeightTerm scalarWeightRoot scalarWeightSquare
  fun_prop

theorem evalScalarTerms_measurable {d : ℕ} (ts : List (ScalarWeightTermData d)) (b : ℝ) :
    Measurable (evalScalarTerms ts b) := by
  induction ts with
  | nil => exact measurable_const
  | cons t ts ih =>
    change Measurable (scalarWeightTerm t.coefficient t.powers t.shift b + evalScalarTerms ts b)
    exact (scalarWeightTerm_measurable t.coefficient t.powers t.shift b).add ih

theorem auxiliaryInverseWeightJet_measurable (is : List (Fin 3)) (n m : ℕ)
    (e : ℝ) (p : GW.Space) : Measurable (auxiliaryInverseWeightJet is n e p m) := by
  unfold auxiliaryInverseWeightJet
  split_ifs with hnm
  · exact (evalScalarTerms_measurable _ _).comp
      ((EuclideanSpace.equiv (Fin 3) ℝ).continuous.measurable.comp ((totalMomentum_measurable m).add_const p))
  · exact measurable_const
  · exact measurable_const

theorem auxiliaryInverseWeightJet_permutation (is : List (Fin 3)) (n m : ℕ)
    (e : ℝ) (p : GW.Space) (tau : Equiv.Perm (Fin m)) (K : GW.Fock.Coordinates m) :
    auxiliaryInverseWeightJet is n e p m (fun i => K (tau i)) = auxiliaryInverseWeightJet is n e p m K := by
  simp only [auxiliaryInverseWeightJet,totalMomentum_permutation]

end Froehlich
