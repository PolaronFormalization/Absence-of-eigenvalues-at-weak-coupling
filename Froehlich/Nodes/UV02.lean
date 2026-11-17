import Froehlich.Nodes.UV02RealShifts

/-! UV02 / lem:cutoffdomain, source1673–1701. At every fixed finite cutoff
and every momentum, the actual full and compressed associated operators
have precisely the free maximal domain and the literal cutoff-field action.
All arbitrary real shifts are the retained GW shifts on that same domain. -/
noncomputable section
namespace Froehlich

def UV02FixedCutoff (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) : Prop :=
  (cutoffHamiltonian g P Λ).domain=(freeFiberOperator P).domain ∧
  (∀ u : (freeFiberOperator P).domain,
    cutoffHamiltonian g P Λ ⟨(u : GW.Fock.Carrier),freeDomain_subset_cutoffDomain g P Λ u.property⟩=
      freeFiberOperator P u+energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property)
        (freeDomainEnergyCoordinate P u)) ∧
  (∀ n : ℕ, (compressedHamiltonian g P n (some Λ)).domain=HighFreePhysicalDomain P n ∧
    ∀ u : HighFreePhysicalDomain P n,
      compressedHamiltonian g P n (some Λ)
        ⟨(u : HighSectorSpace n),highFreeDomain_subset_cutoffDomain g P n Λ u.property⟩=
        highFreeAction P n u+highSectorProject n
          (energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property)
            (highFreeDomainEnergyCoordinate P n u : EnergySpace P))) ∧
  (∀ a : ℝ, (GW.Operators.realShift (cutoffHamiltonian g P Λ) a).domain=(freeFiberOperator P).domain ∧
    ∀ u : (freeFiberOperator P).domain,
      GW.Operators.realShift (cutoffHamiltonian g P Λ) a
        ⟨(u : GW.Fock.Carrier),freeDomain_subset_cutoffDomain g P Λ u.property⟩=
        freeFiberOperator P u+energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property)
          (freeDomainEnergyCoordinate P u)-(a : ℂ) • (u : GW.Fock.Carrier)) ∧
  (∀ (n : ℕ) (a : ℝ),
    (GW.Operators.realShift (compressedHamiltonian g P n (some Λ)) a).domain=HighFreePhysicalDomain P n ∧
    ∀ u : HighFreePhysicalDomain P n,
      GW.Operators.realShift (compressedHamiltonian g P n (some Λ)) a
        ⟨(u : HighSectorSpace n),highFreeDomain_subset_cutoffDomain g P n Λ u.property⟩=
        highFreeAction P n u+highSectorProject n
          (energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property)
            (highFreeDomainEnergyCoordinate P n u : EnergySpace P))-(a : ℂ) • (u : HighSectorSpace n))

theorem finalUV02 (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) : UV02FixedCutoff g P Λ := by
  refine ⟨cutoffDomain_eq_freeDomain g P Λ,cutoff_freeDomain_action g P Λ,?_,?_,?_⟩
  · intro n
    exact ⟨highCutoffDomain_eq_freeDomain g P n Λ,highCutoff_freeDomain_action g P n Λ⟩
  · intro a
    exact ⟨cutoff_realShift_domain g P Λ a,cutoff_realShift_action g P Λ a⟩
  · intro n a
    exact ⟨highCutoff_realShift_domain g P n Λ a,highCutoff_realShift_action g P n Λ a⟩

end Froehlich
