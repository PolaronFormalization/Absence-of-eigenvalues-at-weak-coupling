import Froehlich.Nodes.UV02HighFreeDomainAction
import GW.Operators.InverseOperator

/-! Arbitrary real scalar shifts use the retained GW shift on exactly the
same full domain, including the source shifts e-1+n. -/
noncomputable section
namespace Froehlich

theorem cutoff_realShift_domain (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) (a : ℝ) :
    (GW.Operators.realShift (cutoffHamiltonian g P Λ) a).domain=(freeFiberOperator P).domain :=
  (GW.Operators.realShift_domain _ _).trans (cutoffDomain_eq_freeDomain g P Λ)

theorem highCutoff_realShift_domain (g : ℝ) (P : GW.Space) (n : ℕ)
    (Λ : GW.Operators.PositiveCutoff) (a : ℝ) :
    (GW.Operators.realShift (compressedHamiltonian g P n (some Λ)) a).domain=HighFreePhysicalDomain P n :=
  (GW.Operators.realShift_domain _ _).trans (highCutoffDomain_eq_freeDomain g P n Λ)

theorem cutoff_realShift_action (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (a : ℝ) (u : (freeFiberOperator P).domain) :
    GW.Operators.realShift (cutoffHamiltonian g P Λ) a
      ⟨(u : GW.Fock.Carrier),freeDomain_subset_cutoffDomain g P Λ u.property⟩=
      freeFiberOperator P u+energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property)
        (freeDomainEnergyCoordinate P u)-(a : ℂ) • (u : GW.Fock.Carrier) := by
  change cutoffHamiltonian g P Λ
    ⟨(u : GW.Fock.Carrier),freeDomain_subset_cutoffDomain g P Λ u.property⟩-(a : ℂ) • (u : GW.Fock.Carrier)=_
  rw [cutoff_freeDomain_action]

theorem highCutoff_realShift_action (g : ℝ) (P : GW.Space) (n : ℕ) (Λ : GW.Operators.PositiveCutoff)
    (a : ℝ) (u : HighFreePhysicalDomain P n) :
    GW.Operators.realShift (compressedHamiltonian g P n (some Λ)) a
      ⟨(u : HighSectorSpace n),highFreeDomain_subset_cutoffDomain g P n Λ u.property⟩=
      highFreeAction P n u+highSectorProject n
        (energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property)
          (highFreeDomainEnergyCoordinate P n u : EnergySpace P))-(a : ℂ) • (u : HighSectorSpace n) := by
  change compressedHamiltonian g P n (some Λ)
    ⟨(u : HighSectorSpace n),highFreeDomain_subset_cutoffDomain g P n Λ u.property⟩-(a : ℂ) • (u : HighSectorSpace n)=_
  rw [highCutoff_freeDomain_action]

end Froehlich
