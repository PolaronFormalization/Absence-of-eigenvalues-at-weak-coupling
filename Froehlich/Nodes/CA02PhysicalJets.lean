import Froehlich.Nodes.CA02AuxiliarySymbolDerivatives
import Froehlich.Nodes.CA02MultiplierCoordinates

set_option autoImplicit false

/-! Actual bounded operator candidates for the literal derivative symbols.
Order zero is the existing source G, rather than another definition of G.
Operator norm differentiability is established in the subsequent calculus. -/
noncomputable section
open MeasureTheory
namespace Froehlich

def boundedHighFockAction (n : ℕ) (a : ∀ m, GW.Fock.Coordinates m → ℝ)
    (ha : ∀ m, Measurable (a m)) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ m K, |a m K| ≤ C)
    (hp : ∀ m (tau : Equiv.Perm (Fin m)) K, a m (fun i => K (tau i)) = a m K) :
    HighSectorSpace n →L[ℂ] HighSectorSpace n := by
  let L := (boundedFockAction a ha C hC hb hp).comp (HighSectorSpace n).subtypeL
  apply L.codRestrict (HighSectorSpace n)
  intro f
  apply (highSector_mem_iff n _).mpr
  change highSectorProjection n (boundedFockAction a ha C hC hb hp (f : GW.Fock.Carrier)) =
    boundedFockAction a ha C hC hb hp (f : GW.Fock.Carrier)
  apply lp.ext
  funext m
  rw [highSectorProjection_apply]
  by_cases hnm : n ≤ m
  · rw [if_pos hnm]
  · rw [if_neg hnm]
    have hf := congrArg (fun u : GW.Fock.Carrier => u m) ((highSector_mem_iff n f).mp f.property)
    have hf0 : (f : GW.Fock.Carrier) m = 0 := by
      simpa only [highSectorProjection_apply,if_neg hnm] using hf.symm
    change (0 : GW.Fock.Sector m) = boundedFockSector a ha C hb hp m ((f : GW.Fock.Carrier) m)
    rw [hf0,map_zero]

theorem boundedHighFockAction_ae (n : ℕ) (a : ∀ m, GW.Fock.Coordinates m → ℝ)
    (ha : ∀ m, Measurable (a m)) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ m K, |a m K| ≤ C)
    (hp : ∀ m (tau : Equiv.Perm (Fin m)) K, a m (fun i => K (tau i)) = a m K)
    (f : HighSectorSpace n) (m : ℕ) :
    (fun K => (a m K : ℂ) • physicalSector m ((f : GW.Fock.Carrier) m) K) =ᵐ[GW.Fock.sectorMeasure m]
      physicalSector m ((boundedHighFockAction n a ha C hC hb hp f : GW.Fock.Carrier) m) :=
  boundedFockAction_ae a ha C hC hb hp (f : GW.Fock.Carrier) m

def auxiliaryPhysicalWeightJet (is : List (Fin 3)) (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  match is with
  | [] => auxiliaryPhysicalFreeInverse n e p he
  | i::is => boundedHighFockAction n (auxiliaryInverseWeightJet (i::is) n e p)
      (fun m => auxiliaryInverseWeightJet_measurable (i::is) n m e p)
      (scalarDerivativeCoefficientBound (i::is).length)
      (scalarDerivativeCoefficientBound_nonnegative (i::is).length)
      (fun m K => auxiliaryInverseWeightJet_bound (i::is) n m e p he K)
      (fun m tau K => auxiliaryInverseWeightJet_permutation (i::is) n m e p tau K)

theorem auxiliaryPhysicalWeightJet_nil (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    auxiliaryPhysicalWeightJet [] n e p he = auxiliaryPhysicalFreeInverse n e p he := rfl

theorem auxiliaryPhysicalWeightJet_ae (is : List (Fin 3)) (n m : ℕ)
    (e : ℝ) (p : GW.Space) (he : e ≤ 0) (f : HighSectorSpace n) :
    (fun K => (auxiliaryInverseWeightJet is n e p m K : ℂ) • physicalSector m ((f : GW.Fock.Carrier) m) K)
      =ᵐ[GW.Fock.sectorMeasure m]
      physicalSector m ((auxiliaryPhysicalWeightJet is n e p he f : GW.Fock.Carrier) m) := by
  cases is with
  | nil => exact auxiliaryPhysicalFreeInverse_jet_ae n m e p he f
  | cons i is => exact boundedHighFockAction_ae n _ _ _ _ _ _ f m

theorem auxiliaryPhysicalWeightJet_norm_le (is : List (Fin 3)) (n : ℕ)
    (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    ‖auxiliaryPhysicalWeightJet is n e p he‖ ≤ scalarDerivativeCoefficientBound is.length := by
  apply operator_norm_le_of_ae_multiplier_coordinates
    (HighSectorSpace n).subtypeₗᵢ (HighSectorSpace n).subtypeₗᵢ
    (auxiliaryPhysicalWeightJet is n e p he)
    (fun m K => (auxiliaryInverseWeightJet is n e p m K : ℂ))
    (scalarDerivativeCoefficientBound is.length) (scalarDerivativeCoefficientBound_nonnegative is.length)
  · intro m K
    simpa only [Complex.norm_real,Real.norm_eq_abs] using auxiliaryInverseWeightJet_bound is n m e p he K
  · intro f m
    exact auxiliaryPhysicalWeightJet_ae is n m e p he f

def auxiliaryPhysicalWeightJetChart (n : ℕ) (e : ℝ) (he : e ≤ 0)
    (is : List (Fin 3)) (p : Fin 3 → ℝ) : HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  auxiliaryPhysicalWeightJet is n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he

theorem auxiliaryPhysicalWeightJetChart_ae (is : List (Fin 3)) (n m : ℕ)
    (e : ℝ) (he : e ≤ 0) (p : Fin 3 → ℝ) (f : HighSectorSpace n) :
    (fun K => (auxiliaryInverseWeightJetChart is n e p m K : ℂ) • physicalSector m ((f : GW.Fock.Carrier) m) K)
      =ᵐ[GW.Fock.sectorMeasure m]
      physicalSector m ((auxiliaryPhysicalWeightJetChart n e he is p f : GW.Fock.Carrier) m) :=
  auxiliaryPhysicalWeightJet_ae is n m e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he f

end Froehlich
