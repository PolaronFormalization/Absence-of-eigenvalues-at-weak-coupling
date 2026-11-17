import Froehlich.Nodes.KE01SourceSymmetry
import Froehlich.Nodes.SY01Hamiltonian

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

/- Full original energy-domain uniqueness, with the actual shifted form. -/
include hn he hg hs in
theorem ke01_shiftedWeak_unique (u v : HighEnergySpace (-p) n)
    (h : ∀ w : HighEnergySpace (-p) n,
      (compressedFiberFormData g (-p) n none).form w u -
          ((e-1+(n : ℝ) : ℝ) : ℂ) * ⟪highEnergyEmbedding (-p) n w,highEnergyEmbedding (-p) n u⟫_ℂ =
      (compressedFiberFormData g (-p) n none).form w v -
          ((e-1+(n : ℝ) : ℝ) : ℂ) * ⟪highEnergyEmbedding (-p) n w,highEnergyEmbedding (-p) n v⟫_ℂ) : u = v := by
  let T := auxiliaryCompressedEnergyOperator n e p hn he g
  let Q := auxiliaryCompressedEnergyInverse n e p hn he g hg hs
  have hl : Function.LeftInverse Q T := by
    intro x
    have hh := congrArg (fun A : HighEnergySpace (-p) n →L[ℂ] HighEnergySpace (-p) n => A x)
      (auxiliaryCompressedEnergyInverse_left n e p hn he g hg hs)
    exact hh
  apply hl.injective
  apply ext_inner_left ℂ
  intro w
  exact (auxiliaryCompressedEnergyOperator_spec n e p hn he g w u).trans
    ((h w).trans (auxiliaryCompressedEnergyOperator_spec n e p hn he g w v).symm)

theorem ke01_physicalEnergySolution_shiftedWeak (f : HighSectorSpace n)
    (w : HighEnergySpace (-p) n) :
    (compressedFiberFormData g (-p) n none).form w
        (auxiliaryPhysicalEnergySolution n e p hn he g hg hs f) -
      ((e-1+(n : ℝ) : ℝ) : ℂ) * ⟪highEnergyEmbedding (-p) n w,
        highEnergyEmbedding (-p) n (auxiliaryPhysicalEnergySolution n e p hn he g hg hs f)⟫_ℂ =
      ⟪highEnergyEmbedding (-p) n w,f⟫_ℂ := by
  have h := auxiliaryResolvent_weak n e p hn he g hg hs f w
  change (fiberFormData g (-p) none).form w
      (auxiliaryPhysicalEnergySolution n e p hn he g hg hs f) -
      ((e-1+(n : ℝ) : ℝ) : ℂ) *
        ⟪energyEmbedding (-p) (w : EnergySpace (-p)),
          energyEmbedding (-p) (auxiliaryPhysicalEnergySolution n e p hn he g hg hs f : EnergySpace (-p))⟫_ℂ = _
  calc
    _ = (fiberFormData g (-p) none).form w
        (auxiliaryPhysicalEnergySolution n e p hn he g hg hs f) +
        ((1-(n : ℝ)-e : ℝ) : ℂ) *
        ⟪energyEmbedding (-p) (w : EnergySpace (-p)),
          energyEmbedding (-p) (auxiliaryPhysicalEnergySolution n e p hn he g hg hs f : EnergySpace (-p))⟫_ℂ := by
      push_cast
      ring
    _ = _ := h

theorem auxiliaryPhysicalEnergySolution_conjugation (f : HighSectorSpace n) :
    highEnergyConjugation (-p) n (auxiliaryPhysicalEnergySolution n e p hn he g hg hs f) =
      auxiliaryPhysicalEnergySolution n e p hn he g hg hs (highSectorConjugation n f) := by
  apply ke01_shiftedWeak_unique n e p hn he g hg hs
  intro w
  have hc := compressedWeak_conjugation g (e-1+(n : ℝ)) (-p) n none
    (auxiliaryPhysicalLoad n p f) (auxiliaryPhysicalEnergySolution n e p hn he g hg hs f)
    (ke01_physicalEnergySolution_shiftedWeak n e p hn he g hg hs f)
  rw [hc w,ke01_physicalEnergySolution_shiftedWeak n e p hn he g hg hs]
  change (starRingEnd ℂ) ⟪energyEmbedding (-p)
    (energyConjugation (-p) (w : EnergySpace (-p))), (f : GW.Fock.Carrier)⟫_ℂ =
      ⟪energyEmbedding (-p) (w : EnergySpace (-p)), fockConjugation (f : GW.Fock.Carrier)⟫_ℂ
  rw [energyConjugation_intertwines,fockConjugation_inner_flip]

end Froehlich
