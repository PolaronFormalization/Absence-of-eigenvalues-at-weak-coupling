import Froehlich.Nodes.PT02LocalSource

/-! The local L² PT02 identity follows by equality of two actual cutoff limits. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Froehlich
variable (e : ℝ) (p : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)
  (K : Set GW.Space) (hK : MeasurableSet K)

theorem cutoffGroundSource_pullthrough_local (Λ : GW.Operators.PositiveCutoff) :
    LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K
      (annihilationField (cutoffGroundSourceNumber e p he g hg hs Λ)) =
    (HighSectorSpace 0).subtypeL.compLp
      (localCutoffInverseField 0 e p (by norm_num) he g hg hs K hK Λ
        (sourcePullthroughLocalField K
          (energyEmbedding (-p) (cutoffGroundSourceEnergy e p he g hg hs Λ : EnergySpace (-p)))
          (fun k => cutoffFormFactorL2 g Λ.val Λ.property k)
          ((Lp.memLp (cutoffFormFactorL2 g Λ.val Λ.property)).restrict K))) := by
  let S := sourcePullthroughLocalField K
    (energyEmbedding (-p) (cutoffGroundSourceEnergy e p he g hg hs Λ : EnergySpace (-p)))
    (fun k => cutoffFormFactorL2 g Λ.val Λ.property k)
    ((Lp.memLp (cutoffFormFactorL2 g Λ.val Λ.property)).restrict K)
  let T := localCutoffInverseField 0 e p (by norm_num) he g hg hs K hK Λ S
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ K
      (annihilationField (cutoffGroundSourceNumber e p he g hg hs Λ)),
    (HighSectorSpace 0).subtypeL.coeFn_compLp T,
    localCutoffInverseField_ae 0 e p (by norm_num) he g hg hs K hK Λ S,
    sourcePullthroughLocalField_physical K
      (energyEmbedding (-p) (cutoffGroundSourceEnergy e p he g hg hs Λ : EnergySpace (-p)))
      (fun k => cutoffFormFactorL2 g Λ.val Λ.property k)
      ((Lp.memLp (cutoffFormFactorL2 g Λ.val Λ.property)).restrict K),
    ae_restrict_of_ae (s := K) (cutoffGroundSource_pullthrough e p he g hg hs Λ),
    ae_restrict_of_ae (s := K) (cutoffFormFactorL2_ae g Λ.val Λ.property)] with k hl hj ht hsource hp hv
  change (S k : GW.Fock.Carrier) = _ at hsource
  rw [hv] at hsource
  rw [hl,hj,ht]
  rw [hp]
  change (cutoffFormFactor g Λ.val k : ℂ) •
    cutoffAuxiliaryZ e (p+k) he Λ g hg hs _ =
      (cutoffAuxiliaryResolvent 0 e (p+k) he Λ g hg hs (S k) : GW.Fock.Carrier)
  rw [←map_smul,←hsource]
  exact cutoffAuxiliaryExtendedResolvent_on_high 0 e (p+k) he Λ g hg hs (S k)

theorem groundSource_pullthrough_local (hKb : Bornology.IsBounded K)
    (R : ℝ) (hKR : ∀ k ∈ K, ‖k‖ ≤ R) :
    LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K
      (annihilationField (groundSourceNumber e p he g hg hs)) =
    (HighSectorSpace 0).subtypeL.compLp
      (localSingularInverseField 0 e p (by norm_num) he g hg hs K hK hKb
        (sourcePullthroughLocalField K (auxiliaryGroundSourceVector e p he g hg hs)
          (fun k => (fiberFormFactor g k : ℂ))
          (regularSource_local_formFactor_memLp g K hK R hKR))) := by
  have hl := ((LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K).continuous.tendsto _).comp
    (cutoffGroundSourceAnnihilation_tendsto e p he g hg hs)
  have hr := ((HighSectorSpace 0).subtypeL.compLpL 2 (volume.restrict K)).continuous.tendsto _
    |>.comp (localCutoffInverseField_tendsto_varying 0 e p (by norm_num) he g hg hs K hK hKb
      _ _ (cutoffSourcePullthroughLocalField_tendsto e p he g hg hs K hK R hKR))
  apply tendsto_nhds_unique hl
  apply hr.congr'
  exact Eventually.of_forall (fun Λ => (cutoffGroundSource_pullthrough_local e p he g hg hs K hK Λ).symm)

end Froehlich
