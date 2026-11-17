import Froehlich.Nodes.KA01TwoParticle
import Froehlich.Nodes.FC07Interpretation
import Froehlich.Nodes.FB02Vacuum

set_option autoImplicit false

/-! The actual two-particle creation source belongs to the number domain,
and its annihilation field has the exact symmetric two-term formula.
Neither one-particle input is assumed to have bounded momentum support. -/
noncomputable section
open MeasureTheory
namespace Froehlich

theorem oneToHighMap_lowProjection (v f : GW.OnePhonon) :
    lowSectorProjection 2 (oneToHighMap v f : GW.Fock.Carrier) = (oneToHighMap v f : GW.Fock.Carrier) := by
  apply lowSectorProjection_eq_of_bound
  intro n hn
  rw [oneToHighMap_physical,lp.single_apply_ne _ _ _ (show n ≠ 2 by omega)]

def oneToHighNumberMap (v : GW.OnePhonon) : GW.OnePhonon →L[ℂ] NumberFormSpace :=
  (finiteRootLift 2).comp ((HighSectorSpace 2).subtypeL.comp (oneToHighMap v))

theorem oneToHighNumberMap_physical (v f : GW.OnePhonon) :
    numberFormEmbedding (oneToHighNumberMap v f) = (oneToHighMap v f : GW.Fock.Carrier) := by
  change numberFormEmbedding (finiteRootLift 2 (oneToHighMap v f : GW.Fock.Carrier)) = _
  rw [finiteRootLift_embedding,oneToHighMap_lowProjection]

theorem oneToHighNumberMap_high (v f : GW.OnePhonon) :
    numberFormEmbedding (oneToHighNumberMap v f) ∈ HighSectorSpace 2 := by
  rw [oneToHighNumberMap_physical]
  exact (oneToHighMap v f).property

theorem finiteRootLift_oneParticle (f : GW.OnePhonon) :
    finiteRootLift 1 (oneParticleInclusion f) = numberOneParticleLift f := by
  apply numberFormEmbedding_injective
  rw [finiteRootLift_embedding,numberFormEmbedding_oneParticleLift]
  apply lowSectorProjection_eq_of_bound
  intro n hn
  rw [oneParticleInclusion_apply,lp.single_apply_ne _ _ _ (show n ≠ 1 by omega)]

theorem finiteCreationMap_oneParticle (v f : GW.OnePhonon) :
    finiteCreationMap 1 v (oneParticleInclusion f) = (oneToHighMap v f : GW.Fock.Carrier) := by
  change creationRestriction v (finiteRootLift 1 (oneParticleInclusion f)) = _
  rw [finiteRootLift_oneParticle,← oneToHighMap_eq_creation]

theorem finiteRootLift_vacuumCore : finiteRootLift 1 GW.Fock.vacuum = coreNumberLift vacuumCore := by
  apply numberFormEmbedding_injective
  rw [finiteRootLift_embedding,coreNumberLift_embedding]
  change lowSectorProjection 1 GW.Fock.vacuum = GW.Fock.vacuum
  apply lowSectorProjection_eq_of_bound
  intro n hn
  cases n with
  | zero => omega
  | succ n => exact GW.Fock.vacuum_succ n

theorem finiteCreationMap_vacuum (v : GW.OnePhonon) :
    finiteCreationMap 1 v GW.Fock.vacuum = oneParticleInclusion v := by
  change creationRestriction v (finiteRootLift 1 GW.Fock.vacuum) = _
  rw [finiteRootLift_vacuumCore,creationRestriction_vacuum]

theorem annihilationField_oneToHighMap (v f : GW.OnePhonon) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      annihilationField (oneToHighNumberMap v f) k =
        f k • oneParticleInclusion v + v k • oneParticleInclusion f := by
  have h := finite_field_creation_actual_CCR 1 v (oneParticleInclusion f)
  have hlow : lowSectorProjection 1 (oneParticleInclusion f) = oneParticleInclusion f := by
    have he := congrArg numberFormEmbedding (finiteRootLift_oneParticle f)
    rw [finiteRootLift_embedding,numberFormEmbedding_oneParticleLift] at he
    exact he
  have hnumber : finiteRootLift 2 (finiteCreationMap 1 v (oneParticleInclusion f)) =
      oneToHighNumberMap v f := by
    rw [finiteCreationMap_oneParticle]
    rfl
  filter_upwards [h,annihilationField_oneParticle_ae f] with k hc hf
  have he := hc.2
  rw [hnumber,finiteRootLift_oneParticle,hf,map_smul,finiteCreationMap_vacuum,hlow] at he
  exact he

end Froehlich
