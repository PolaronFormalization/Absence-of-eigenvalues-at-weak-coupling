import Froehlich.Nodes.FC06
import Froehlich.Nodes.GW06Sectors

/-! The finite-cutoff one-to-high map uses the actual canonical sector-two
creation map. Its Hilbert adjoint acts on every high physical vector. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

theorem sectorTwo_single_high (z : GW.Fock.Sector 2) :
    lp.single (E := GW.Fock.Sector) 2 2 z ∈ HighSectorSpace 2 := by
  apply (highSector_mem_iff 2 _).mpr
  apply lp.ext
  funext n
  rw [highSectorProjection_apply]
  by_cases hn : 2 ≤ n
  · rw [if_pos hn]
  · rw [if_neg hn,lp.single_apply_ne _ _ _ (show n ≠ 2 by omega)]

def oneToHighMap (v : GW.OnePhonon) : GW.OnePhonon →L[ℂ] HighSectorSpace 2 :=
  (((lp.singleContinuousLinearMap ℂ GW.Fock.Sector 2 2).comp
    (GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel v) 1)).comp
      oneParticleCoordinate.toLinearIsometry.toContinuousLinearMap).codRestrict _ (fun f => by
        change lp.single (E := GW.Fock.Sector) 2 2
          (GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel v) 1 (oneParticleCoordinate f)) ∈ HighSectorSpace 2
        exact sectorTwo_single_high _)

theorem oneToHighMap_physical (v f : GW.OnePhonon) :
    (oneToHighMap v f : GW.Fock.Carrier) = lp.single (E := GW.Fock.Sector) 2 2
      (GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel v) 1 (oneParticleCoordinate f)) := rfl

theorem oneToHighMap_bound (v f : GW.OnePhonon) :
    ‖oneToHighMap v f‖ ≤ (Real.sqrt 2 * ‖v‖) * ‖f‖ := by
  change ‖lp.single (E := GW.Fock.Sector) 2 2
    (GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel v) 1 (oneParticleCoordinate f))‖ ≤ _
  rw [lp.norm_single (E := GW.Fock.Sector) (by norm_num : (0 : ℝ≥0∞) < 2)]
  have h := ((GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel v) 1).le_opNorm
    (oneParticleCoordinate f)).trans (mul_le_mul_of_nonneg_right
      (GW.Fock.sectorCreation_norm GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel v) 1)
      (norm_nonneg (oneParticleCoordinate f)))
  rw [oneParticleCoordinate.norm_map,ordinaryKernel_norm] at h
  simpa using h

theorem oneToHighMap_norm (v : GW.OnePhonon) : ‖oneToHighMap v‖ ≤ Real.sqrt 2 * ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  exact oneToHighMap_bound v

theorem oneToHighMap_eq_creation (v f : GW.OnePhonon) :
    (oneToHighMap v f : GW.Fock.Carrier) = creationRestriction v (numberOneParticleLift f) := by
  apply lp.ext
  funext n
  rw [oneToHighMap_physical]
  cases n with
  | zero =>
    rw [creationRestriction_apply,GW.Fock.ordinaryCreation_zero,
      lp.single_apply_ne _ _ _ (by decide : (0 : ℕ) ≠ 2)]
  | succ n =>
    rw [creationRestriction_apply,GW.Fock.ordinaryCreation_succ]
    change (lp.single (E := GW.Fock.Sector) 2 2
      (GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel v) 1 (oneParticleCoordinate f))) (n+1) =
        GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel v) n
          (numberFormEmbedding (numberOneParticleLift f) n)
    rw [numberFormEmbedding_oneParticleLift,oneParticleInclusion_apply]
    by_cases hn : n = 1
    · subst n
      rw [lp.single_apply_self,lp.single_apply_self]
    · rw [lp.single_apply_ne _ _ _ (show n+1 ≠ 2 by omega),lp.single_apply_ne _ _ _ hn,map_zero]

def oneToHighAdjoint (v : GW.OnePhonon) : HighSectorSpace 2 →L[ℂ] GW.OnePhonon :=
  (oneToHighMap v).adjoint

theorem oneToHighAdjoint_pairing (v f : GW.OnePhonon) (z : HighSectorSpace 2) :
    ⟪oneToHighMap v f,z⟫_ℂ = ⟪f,oneToHighAdjoint v z⟫_ℂ :=
  ((oneToHighMap v).adjoint_inner_right f z).symm

theorem oneToHighAdjoint_norm (v : GW.OnePhonon) : ‖oneToHighAdjoint v‖ ≤ Real.sqrt 2 * ‖v‖ := by
  calc
    ‖oneToHighAdjoint v‖ = ‖oneToHighMap v‖ := ContinuousLinearMap.adjoint.norm_map _
    _ ≤ _ := oneToHighMap_norm v

end Froehlich
