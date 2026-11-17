import Froehlich.Nodes.RS01AuxiliaryFields
import Froehlich.Nodes.SP03PhysicalInverse
import Froehlich.Nodes.SP01ScalarIdentities

/-! The auxiliary definitions agree with the earlier high inverse and
vacuum root. No new reference energy is selected by these identifications. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

variable (e : ℝ) (p : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1/4) (hM : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem auxiliaryResolvent_two_eq (P : GW.Space)
    (heLower : -sectorEnergyConstant*|g|^2 ≤ e) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8) :
    auxiliaryResolvent 2 e (-P) he g (hg.trans (by norm_num)) hM =
      twoSectorPhysicalInverse g e 0 P hg heLower he.2 (by norm_num) hsmall := by
  have ha := auxiliaryResolvent_isResolvent 2 e (-P) (by norm_num) he g (hg.trans (by norm_num)) hM
  have hscalar : e-1+(2 : ℝ) = e+1 := by ring
  have ha' : GW.Operators.IsResolvent (compressedHamiltonian g P 2 none) ((e+1 : ℝ) : ℂ)
      (auxiliaryResolvent 2 e (-P) he g (hg.trans (by norm_num)) hM) := by
    simpa only [neg_neg,Nat.cast_ofNat,hscalar] using ha
  have hleft : twoSectorEnergyInverse g e 0 P hg heLower he.2 (by norm_num) hsmall *
      twoSectorOperator g P (e+1-0) = 1 := by
    apply ContinuousLinearMap.ext
    intro u
    exact twoSectorEnergyInverse_left_apply g e 0 P hg heLower he.2 (by norm_num) hsmall u
  have hright : twoSectorOperator g P (e+1-0) *
      twoSectorEnergyInverse g e 0 P hg heLower he.2 (by norm_num) hsmall = 1 := by
    apply ContinuousLinearMap.ext
    intro u
    exact twoSectorEnergyInverse_right_apply g e 0 P hg heLower he.2 (by norm_num) hsmall u
  have hb := physicalEnergyInverse_isResolvent (compressedFiberFormData g P 2 none) (e+1-0)
    (twoSectorOperator g P (e+1-0)) (twoSectorEnergyInverse g e 0 P hg heLower he.2 (by norm_num) hsmall)
    (twoSectorOperator_spec g P (e+1-0)) hleft hright
  have hb' : GW.Operators.IsResolvent (compressedHamiltonian g P 2 none) ((e+1 : ℝ) : ℂ)
      (twoSectorPhysicalInverse g e 0 P hg heLower he.2 (by norm_num) hsmall) := by
    change GW.Operators.IsResolvent (GW.Operators.formOperator (compressedFiberFormData g P 2 none))
      ((e+1 : ℝ) : ℂ) (physicalEnergyInverse (compressedFiberFormData g P 2 none)
        (twoSectorEnergyInverse g e 0 P hg heLower he.2 (by norm_num) hsmall))
    simpa only [sub_zero] using hb
  exact GW.Operators.isResolvent_unique ha' hb'

theorem auxiliaryX_eq_twoSector (P : GW.Space)
    (heLower : -sectorEnergyConstant*|g|^2 ≤ e) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8) :
    auxiliaryX e he g (hg.trans (by norm_num)) hM P =
      (HighSectorSpace 2).subtypeL.comp
        ((twoSectorPhysicalInverse g e 0 P hg heLower he.2 (by norm_num) hsmall).comp (highSectorProject 2)) := by
  unfold auxiliaryX auxiliaryExtendedResolvent
  rw [auxiliaryResolvent_two_eq e he g hg hM P heLower hsmall]

theorem auxiliarySelfEnergy_at_vacuum_root (hthr : e < nonvacuumThreshold g)
    (hroot : vacuumSchurFunction g (-p) hg ⟨e,hthr⟩ = 0) :
    auxiliarySelfEnergy e p he g (hg.trans (by norm_num)) hM = e-‖p‖^2 := by
  let hg1 : |g| ≤ 1 := hg.trans (by norm_num)
  let u := auxiliaryGroundSourceEnergy e p he g hg1 hM
  have hx : u = vacuumSourceSolution g (-p) e hg hthr := by
    apply compressedCoerciveSolution_unique (nonvacuumCoercivity g (-p) e hg hthr)
      (highFiberSourceLoad g (-p) 1) u
    intro w
    have hi : ⟪highEnergyEmbedding (-p) 1 w,highEnergyEmbedding (-p) 1 u⟫_ℂ =
        ⟪energyEmbedding (-p) (w : EnergySpace (-p)),energyEmbedding (-p) (u : EnergySpace (-p))⟫_ℂ := by
      change ⟪(highEnergyEmbedding (-p) 1 w : GW.Fock.Carrier),
        (highEnergyEmbedding (-p) 1 u : GW.Fock.Carrier)⟫_ℂ = _
      rw [highEnergyEmbedding_apply,highEnergyEmbedding_apply]
    rw [hi]
    exact auxiliaryGroundSourceEnergy_weak e p he g hg1 hM w
  have hv := vacuumSourceSolution_sourceValue g (-p) hg (⟨e,hthr⟩ : Set.Iio (nonvacuumThreshold g))
  change -(highFiberSourceLoad g (-p) 1 u).re = e-‖p‖^2
  rw [hx,hv,Complex.ofReal_re]
  change ‖-p‖^2-e-vacuumSelfEnergy g (-p) hg ⟨e,hthr⟩ = 0 at hroot
  rw [norm_neg] at hroot
  linarith

theorem auxiliarySelfEnergy_zero_of_vacuum_root (hthr : e < nonvacuumThreshold g)
    (hroot : vacuumSchurFunction g 0 hg ⟨e,hthr⟩ = 0) :
    auxiliarySelfEnergy e 0 he g (hg.trans (by norm_num)) hM = e := by
  have h := auxiliarySelfEnergy_at_vacuum_root e 0 he g hg hM hthr (by simpa only [neg_zero] using hroot)
  simpa only [norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero] using h

end Froehlich
