import Froehlich.Nodes.UV02FreeWeights
import Froehlich.Nodes.FD02Weights

/-! The literal positive symbol F+c used at one fixed finite cutoff. -/
noncomputable section
open MeasureTheory
namespace Froehlich

def freeShiftWeight (P : GW.Space) (c : ℝ) (n : ℕ) (K : GW.Fock.Coordinates n) : ℝ :=
  freeSymbol P n K+c

theorem freeShiftWeight_measurable (P : GW.Space) (c : ℝ) (n : ℕ) :
    Measurable (freeShiftWeight P c n) := (freeSymbol_measurable P n).add_const c

theorem freeShiftWeight_permutation (P : GW.Space) (c : ℝ) (n : ℕ)
    (tau : Equiv.Perm (Fin n)) (K : GW.Fock.Coordinates n) :
    freeShiftWeight P c n (fun i => K (tau i))=freeShiftWeight P c n K := by
  simp only [freeShiftWeight,freeSymbol_permutation]

theorem freeShiftWeight_lower (P : GW.Space) (c : ℝ) (hc : 1 ≤ c) (n : ℕ) (K : GW.Fock.Coordinates n) :
    1 ≤ freeShiftWeight P c n K := by
  have h := freeSymbol_nonneg P n K
  unfold freeShiftWeight
  linarith

theorem freeShiftWeight_number_ratio_sq (P : GW.Space) (c : ℝ) (hc : 1 ≤ c)
    (n : ℕ) (K : GW.Fock.Coordinates n) :
    (Real.sqrt ((n : ℝ)+1)/freeShiftWeight P c n K)^2 ≤ 1/c := by
  exact freeShift_number_sqrt_ratio_sq (‖totalMomentum n K-P‖^2) c n (sq_nonneg _) hc

def freeShiftWeightedGraph (P : GW.Space) (c : ℝ) (hc : 1 ≤ c) :
    GW.Spaces.WeightedGraph GW.Fock.Carrier GW.Fock.Carrier :=
  fockWeightedGraph (freeShiftWeight P c) (freeShiftWeight_measurable P c)
    (freeShiftWeight_lower P c hc) (freeShiftWeight_permutation P c)

end Froehlich
