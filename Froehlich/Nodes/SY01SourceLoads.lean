import Froehlich.Nodes.SY01CompressedForms
import Froehlich.Nodes.LD01
import Froehlich.Nodes.SY01Annihilation
import Froehlich.Nodes.KA01NumberPairing

/-! Real-even singular source covariance on actual energy domains. Only
the absolutely integrable LD01 pairing is used; v_g is never an L² vector. -/
noncomputable section
open MeasureTheory Filter
namespace Froehlich

theorem extraction_physical_representative (u : GW.Fock.Carrier) :
    (physicalSector 1 (u 1) : GW.Fock.Coordinates 1 → ℂ) =ᵐ[GW.Fock.sectorMeasure 1]
      (fun K => oneParticleExtraction u (K 0)) := by
  exact oneParticleExtraction_representative_ae u

theorem extraction_conjugation_ae (u : GW.Fock.Carrier) :
    oneParticleExtraction (fockConjugation u) =ᵐ[volume]
      (fun k => (starRingEnd ℂ) (oneParticleExtraction u k)) := by
  have hm : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) GW.Space).symm
      (volume : Measure GW.Space) (GW.Fock.sectorMeasure 1) :=
    (measurePreserving_funUnique (volume : Measure GW.Space) (Fin 1)).symm _
  filter_upwards [hm.quasiMeasurePreserving.ae (extraction_physical_representative (fockConjugation u)),
    hm.quasiMeasurePreserving.ae (extraction_physical_representative u),
    hm.quasiMeasurePreserving.ae (fockConjugation_physical u 1)] with k hJ hu hc
  exact hJ.symm.trans (hc.trans (congrArg (starRingEnd ℂ) hu))

theorem extraction_reflection_ae (u : GW.Fock.Carrier) :
    oneParticleExtraction (fockReflection u) =ᵐ[volume] (fun k => oneParticleExtraction u (-k)) := by
  have hm : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) GW.Space).symm
      (volume : Measure GW.Space) (GW.Fock.sectorMeasure 1) :=
    (measurePreserving_funUnique (volume : Measure GW.Space) (Fin 1)).symm _
  have hu := (configurationNegation_preserving 1).quasiMeasurePreserving.ae
    (extraction_physical_representative u)
  filter_upwards [hm.quasiMeasurePreserving.ae (extraction_physical_representative (fockReflection u)),
    hm.quasiMeasurePreserving.ae hu,
    hm.quasiMeasurePreserving.ae (fockReflection_physical u 1)] with k hR hu hr
  exact hR.symm.trans (hr.trans hu)

theorem fiberSourceLoad_conjugation (g : ℝ) (P : GW.Space) (w : EnergySpace P) :
    fiberSourceLoad g P (energyConjugation P w) = (starRingEnd ℂ) (fiberSourceLoad g P w) := by
  rw [fiberSourceLoad_integral,energyConjugation_intertwines,fiberSourceLoad_integral]
  change (∫ k : GW.Space, (starRingEnd ℂ) (oneParticleExtraction (fockConjugation (energyEmbedding P w)) k) *
    (fiberFormFactor g k : ℂ)) = (starRingEnd ℂ)
      (∫ k : GW.Space, (starRingEnd ℂ) (oneParticleExtraction (energyEmbedding P w) k) * (fiberFormFactor g k : ℂ))
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [extraction_conjugation_ae (energyEmbedding P w)] with k hk
  change (starRingEnd ℂ) (oneParticleExtraction (fockConjugation (energyEmbedding P w)) k) *
      (fiberFormFactor g k : ℂ) = (starRingEnd ℂ)
        ((starRingEnd ℂ) (oneParticleExtraction (energyEmbedding P w) k) * (fiberFormFactor g k : ℂ))
  rw [hk]
  simp only [map_mul,starRingEnd_self_apply,Complex.conj_ofReal]

theorem fiberSourceLoad_conjugation_for_weak (g : ℝ) (P : GW.Space) (w : EnergySpace P) :
    (starRingEnd ℂ) (fiberSourceLoad g P (energyConjugation P w)) = fiberSourceLoad g P w := by
  rw [fiberSourceLoad_conjugation,starRingEnd_self_apply]

theorem fiberSourceLoad_reflection (g : ℝ) (P : GW.Space) (w : EnergySpace P) :
    fiberSourceLoad g (-P) (energyReflection P w) = fiberSourceLoad g P w := by
  rw [fiberSourceLoad_integral,energyReflection_intertwines,fiberSourceLoad_integral]
  calc
    _ = ∫ k : GW.Space, (starRingEnd ℂ) (oneParticleExtraction (energyEmbedding P w) (-k)) *
        (fiberFormFactor g (-k) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [extraction_reflection_ae (energyEmbedding P w)] with k hk
      rw [hk]
      simp only [fiberFormFactor,norm_neg]
    _ = _ := space_negation_preserving.integral_comp
      (MeasurableEquiv.neg GW.Space).measurableEmbedding
      (fun k => (starRingEnd ℂ) (oneParticleExtraction (energyEmbedding P w) k) * (fiberFormFactor g k : ℂ))

def highFiberSourceLoad (g : ℝ) (P : GW.Space) (n : ℕ) : ConjugateLoad (HighEnergySpace P n) :=
  (fiberSourceLoad g P).comp (HighEnergySpace P n).subtypeL

theorem highFiberSourceLoad_conjugation (g : ℝ) (P : GW.Space) (n : ℕ) (w : HighEnergySpace P n) :
    (starRingEnd ℂ) (highFiberSourceLoad g P n (highEnergyConjugation P n w)) = highFiberSourceLoad g P n w :=
  fiberSourceLoad_conjugation_for_weak g P (w : EnergySpace P)

theorem highFiberSourceLoad_reflection (g : ℝ) (P : GW.Space) (n : ℕ) (w : HighEnergySpace P n) :
    highFiberSourceLoad g (-P) n (highEnergyReflection P n w) = highFiberSourceLoad g P n w :=
  fiberSourceLoad_reflection g P (w : EnergySpace P)

end Froehlich
