import Froehlich.Nodes.RS02SourceJetsBounds
import Froehlich.Nodes.SY01SourceLoads

set_option autoImplicit false

/-! The actual normalized Riesz source equals the literal one-particle L2
vector. The equality uses only genuine energy loads and absolutely
integrable L2 pairings; the uncut form factor is never a Hilbert vector. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

theorem extraction_auxiliaryPhysicalWeightJet_ae (is : List (Fin 3)) (n : ℕ) (e : ℝ)
    (p : GW.Space) (he : e ≤ 0) (f : HighSectorSpace n) :
    oneParticleExtraction (auxiliaryPhysicalWeightJet is n e p he f : GW.Fock.Carrier) =ᵐ[volume]
      (fun k => (auxiliaryInverseWeightJet is n e p 1 (fun _ => k) : ℂ)*
        oneParticleExtraction (f : GW.Fock.Carrier) k) := by
  have hm : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) GW.Space).symm
      (volume : Measure GW.Space) (GW.Fock.sectorMeasure 1) :=
    (measurePreserving_funUnique (volume : Measure GW.Space) (Fin 1)).symm _
  filter_upwards [hm.quasiMeasurePreserving.ae (extraction_physical_representative
      (auxiliaryPhysicalWeightJet is n e p he f : GW.Fock.Carrier)),
    hm.quasiMeasurePreserving.ae (extraction_physical_representative (f : GW.Fock.Carrier)),
    hm.quasiMeasurePreserving.ae (auxiliaryPhysicalWeightJet_ae is n 1 e p he f)] with k hout hin hjet
  simp only [smul_eq_mul] at hjet
  exact hout.symm.trans (hjet.symm.trans (congrArg
    (fun z : ℂ => (auxiliaryInverseWeightJet is n e p 1 (fun _ => k) : ℂ)*z) hin))

def auxiliarySourceJetHigh (is : List (Fin 3)) (g e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    HighSectorSpace 1 :=
  ⟨oneParticleInclusion (auxiliarySourceJetL2 is g e p he),by
    apply (highSector_mem_iff 1 _).mpr
    apply lp.ext
    funext m
    rw [highSectorProjection_apply]
    by_cases hm : 1 ≤ m
    · rw [if_pos hm]
    · rw [if_neg hm,oneParticleInclusion_apply,
        lp.single_apply_ne 2 1 (oneParticleCoordinate (auxiliarySourceJetL2 is g e p he)) (by omega : m ≠ 1)]⟩

theorem auxiliarySourceJetHigh_norm (is : List (Fin 3)) (g e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    ‖auxiliarySourceJetHigh is g e p he‖ = ‖auxiliarySourceJetL2 is g e p he‖ :=
  oneParticleInclusion_norm _

theorem auxiliaryNormalizedSource_eq_sourceJetHigh (g e : ℝ) (p : GW.Space)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) :
    auxiliaryNormalizedSource g e p he.2 = auxiliarySourceJetHigh [] g e p he.2 := by
  apply Eq.symm
  apply loadRiesz_unique
  intro f
  change fiberSourceLoad g (-p) (auxiliaryEnergyLift 1 e p he.2 f) =
    ⟪(f : GW.Fock.Carrier),oneParticleInclusion (auxiliarySourceJetL2 [] g e p he.2)⟫_ℂ
  rw [fiberSourceLoad_integral,auxiliaryEnergyLift_physical 1 e p (by norm_num) he]
  have hp := oneParticleInclusion.adjoint_inner_left (auxiliarySourceJetL2 [] g e p he.2)
    (f : GW.Fock.Carrier)
  rw [oneParticleInclusion_adjoint] at hp
  rw [← hp,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [extraction_auxiliaryPhysicalWeightJet_ae [] 1 e p he.2 f,
    auxiliarySourceJetL2_ae [] g e p he.2] with k hG hz
  simp only [auxiliaryPhysicalWeightJet_nil] at hG
  rw [hG,hz]
  simp only [auxiliarySourceJetFunction,RCLike.inner_apply',map_mul,Complex.conj_ofReal]
  ring

end Froehlich
