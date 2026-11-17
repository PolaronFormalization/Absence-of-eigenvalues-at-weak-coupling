import Froehlich.Nodes.UV01Coupling

/-! Actual isolated one-particle energy spaces at different momenta have
bounded physical identity maps. These fix the Schur correction carrier. -/
noncomputable section
namespace Froehlich

def oneParticleEnergyCoordinateChange (P Q : GW.Space) :
    OneParticleEnergySpace Q →L[ℂ] OneParticleEnergySpace P :=
  (oneParticleEnergyProjection P).comp ((energyCoordinateChange P Q).comp (onePhononEnergyLift Q))

theorem oneParticleEnergyCoordinateChange_physical (P Q : GW.Space) (f : OneParticleEnergySpace Q) :
    oneParticleEnergyEmbedding P (oneParticleEnergyCoordinateChange P Q f) = oneParticleEnergyEmbedding Q f := by
  change oneParticleEnergyEmbedding P
    (oneParticleEnergyProjection P (energyCoordinateChange P Q (onePhononEnergyLift Q f))) = _
  rw [oneParticleEnergyProjection_intertwines,energyCoordinateChange_intertwines,
    onePhononEnergyLift_physical,oneParticleExtraction_inclusion]

theorem oneParticleEnergyCoordinateChange_cancel (P Q : GW.Space) (f : OneParticleEnergySpace P) :
    oneParticleEnergyCoordinateChange P Q (oneParticleEnergyCoordinateChange Q P f)=f := by
  apply oneParticleEnergyEmbedding_injective P
  rw [oneParticleEnergyCoordinateChange_physical,oneParticleEnergyCoordinateChange_physical]

theorem oneParticleEnergyCoordinateChange_norm_le (P Q : GW.Space) :
    ‖oneParticleEnergyCoordinateChange P Q‖ ≤ Real.sqrt 2*momentumChangeConstant P Q := by
  have hC : 0 ≤ momentumChangeConstant P Q := Real.sqrt_nonneg _
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) hC)
  intro f
  change ‖oneParticleEnergyProjection P (energyCoordinateChange P Q (onePhononEnergyLift Q f))‖ ≤ _
  calc
    _ ≤ ‖energyCoordinateChange P Q (onePhononEnergyLift Q f)‖ := oneParticleEnergyProjection_norm_le P _
    _ ≤ ‖energyCoordinateChange P Q‖*‖onePhononEnergyLift Q f‖ := (energyCoordinateChange P Q).le_opNorm _
    _ ≤ momentumChangeConstant P Q*(Real.sqrt 2*‖f‖) := mul_le_mul
      (energyCoordinateChange_norm_le P Q) (onePhononEnergyLift_norm_le Q f) (norm_nonneg _) hC
    _ = _ := by ring

theorem oneParticleEnergyCoordinateChange_norm_sq (P P0 : GW.Space) (R : ℝ)
    (hR : 0 ≤ R) (hdist : ‖P-P0‖ ≤ R) :
    ‖oneParticleEnergyCoordinateChange P P0‖^2 ≤ 4*(1+R^2) := by
  have hC : 0 ≤ momentumChangeConstant P P0 := Real.sqrt_nonneg _
  have hsq := (sq_le_sq₀ (ContinuousLinearMap.opNorm_nonneg (oneParticleEnergyCoordinateChange P P0))
    (mul_nonneg (Real.sqrt_nonneg 2) hC)).mpr (oneParticleEnergyCoordinateChange_norm_le P P0)
  rw [mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)] at hsq
  unfold momentumChangeConstant at hsq
  rw [Real.sq_sqrt (by positivity)] at hsq
  have hd := (sq_le_sq₀ (norm_nonneg (P-P0)) hR).mpr hdist
  linarith

end Froehlich
