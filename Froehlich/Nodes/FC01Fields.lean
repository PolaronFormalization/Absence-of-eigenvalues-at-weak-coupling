import Froehlich.Nodes.FC01
import Froehlich.Nodes.GW04

/-! Actual smeared fields preserve the bounded momentum, finite sector core. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

theorem kernelRepresentative_physical (n : ℕ) (u : GW.Fock.Sector n) :
    GW.Fock.kernelFixedInclusion n (GW.Fock.ordinarySectorKernel n u) =
      physicalSector n u := by
  cases n <;> rfl

theorem ae_coordinate_deleted (n : ℕ) (j : Fin (n+1))
    {p : GW.Space → Prop} {q : GW.Fock.Coordinates n → Prop}
    (hp : ∀ᵐ k ∂(volume : Measure GW.Space), p k)
    (hq : ∀ᵐ k ∂GW.Fock.sectorMeasure n, q k) :
    ∀ᵐ k ∂GW.Fock.sectorMeasure (n+1), p (k j) ∧ q (fun i => k (j.succAbove i)) := by
  have hp' := (GW.Fock.splitCoordinates_preserving n j).quasiMeasurePreserving.ae
    ((Measure.quasiMeasurePreserving_fst (μ := (volume : Measure GW.Space))
      (ν := GW.Fock.sectorMeasure n)).ae hp)
  have hq' := (GW.Fock.splitCoordinates_preserving n j).quasiMeasurePreserving.ae
    ((Measure.quasiMeasurePreserving_snd (μ := (volume : Measure GW.Space))
      (ν := GW.Fock.sectorMeasure n)).ae hq)
  simpa only [GW.Fock.splitCoordinates_apply] using hp'.and hq'

theorem configurationBall_of_coordinate_deleted (n : ℕ) (j : Fin (n+1))
    (k : GW.Fock.Coordinates (n+1)) (R S : ℝ)
    (hj : ‖k j‖ ≤ S) (hrest : (fun i => k (j.succAbove i)) ∈ configurationBall n R) :
    k ∈ configurationBall (n+1) (max R S) := by
  intro i
  rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨l,rfl⟩
  · exact hj.trans (le_max_right _ _)
  · exact (hrest l).trans (le_max_left _ _)

theorem sectorCreation_bounded_support (f : GW.OnePhonon) (n : ℕ)
    (u : GW.Fock.Sector n) (R S : ℝ)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), S < ‖k‖ → f k = 0)
    (hu : ∀ᵐ k ∂GW.Fock.sectorMeasure n,
      k ∉ configurationBall n R → physicalSector n u k = 0) :
    ∀ᵐ k ∂GW.Fock.sectorMeasure (n+1),
      k ∉ configurationBall (n+1) (max R S) →
        physicalSector (n+1)
          (GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n u) k = 0 := by
  classical
  have hslots := ae_all_iff.mpr (fun j : Fin (n+1) => ae_coordinate_deleted n j hf hu)
  filter_upwards [GW.Fock.ordinaryCreationSector_ae f n u, hslots] with k hk hs
  intro hout
  change GW.Fock.sectorInclusion n
    (GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n u) k = 0
  rw [hk]
  suffices hz : (∑ j : Fin (n+1), f (k j) *
      (GW.Fock.ordinarySectorKernel n u : GW.Fock.AmbientSector n)
        (fun i => k (j.succAbove i))) = 0 by rw [hz, mul_zero]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : S < ‖k j‖
  · rw [(hs j).1 hj, zero_mul]
  · have hrest : (fun i => k (j.succAbove i)) ∉ configurationBall n R := by
      intro hrest
      exact hout (configurationBall_of_coordinate_deleted n j k R S (le_of_not_gt hj) hrest)
    have hz := (hs j).2 hrest
    have he := kernelRepresentative_physical n u
    have he' := congrArg (fun v : GW.Fock.AmbientSector n => v (fun i => k (j.succAbove i))) he
    have hz' : (GW.Fock.ordinarySectorKernel n u : GW.Fock.AmbientSector n)
        (fun i => k (j.succAbove i)) = 0 := he'.trans hz
    rw [hz', mul_zero]

theorem sectorMomentumCutoff_fixed_iff (R : ℝ) (n : ℕ) (u : GW.Fock.Sector n) :
    sectorMomentumCutoff R n u = u ↔
      ∀ᵐ k ∂GW.Fock.sectorMeasure n,
        k ∉ configurationBall n R → physicalSector n u k = 0 := by
  constructor
  · intro he
    have h := sectorMomentumCutoff_ae R n u
    rw [he] at h
    filter_upwards [h] with k hk
    intro hout
    have hi : configurationIndicator n R k = 0 := by simp [configurationIndicator, hout]
    rw [hi, zero_smul] at hk
    exact hk.symm
  · intro hs
    apply (physicalSector n).injective
    apply Lp.ext
    filter_upwards [sectorMomentumCutoff_ae R n u, hs] with k hk hs
    by_cases hm : k ∈ configurationBall n R
    · have hi : configurationIndicator n R k = 1 := by simp [configurationIndicator, hm]
      simpa only [hi, one_smul] using hk.symm
    · have hi : configurationIndicator n R k = 0 := by simp [configurationIndicator, hm]
      rw [hi, zero_smul] at hk
      exact hk.symm.trans (hs hm).symm

theorem sectorCurrying_bounded_support (n : ℕ) (u : GW.Fock.Sector (n+1)) (R : ℝ)
    (hu : ∀ᵐ K ∂GW.Fock.sectorMeasure (n+1),
      K ∉ configurationBall (n+1) R → physicalSector (n+1) u K = 0) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∀ᵐ K ∂GW.Fock.sectorMeasure n,
      K ∉ configurationBall n R → physicalSector n (sectorCurrying n u k) K = 0 := by
  have hp := Measure.ae_ae_of_ae_prod
    ((GW.Fock.splitCoordinates_inverse_preserving n 0).quasiMeasurePreserving.ae hu)
  filter_upwards [hp, sectorCurrying_sections n u] with k hk hs
  filter_upwards [hk, hs] with K hK hsection
  intro hout
  have hinsert : (GW.Fock.splitCoordinates n 0).symm (k,K) ∉ configurationBall (n+1) R := by
    intro hi
    apply hout
    intro i
    have hh := hi ((0 : Fin (n+1)).succAbove i)
    rwa [GW.Fock.insertCoordinate_succAbove] at hh
  have hz := hK hinsert
  have he := congrArg (fun v : GW.Fock.AmbientSector n => v K) (kernelRepresentative_physical n (sectorCurrying n u k))
  exact he.symm.trans (hsection.trans hz)

theorem contraction_bounded_support (f : GW.OnePhonon) (n : ℕ)
    (q : Lp (GW.Fock.Sector n) 2 (volume : Measure GW.Space)) (R : ℝ)
    (hq : ∀ᵐ k ∂(volume : Measure GW.Space), ∀ᵐ K ∂GW.Fock.sectorMeasure n,
      K ∉ configurationBall n R → physicalSector n (q k) K = 0) :
    ∀ᵐ K ∂GW.Fock.sectorMeasure n,
      K ∉ configurationBall n R → physicalSector n (GW.Fock.contraction volume f q) K = 0 := by
  have hfix : GW.Fock.amplify volume (sectorMomentumCutoff R n) q = q := by
    apply Lp.ext
    filter_upwards [GW.Fock.amplify_ae volume (sectorMomentumCutoff R n) q, hq] with k hk hs
    exact hk.trans ((sectorMomentumCutoff_fixed_iff R n (q k)).mpr hs)
  apply (sectorMomentumCutoff_fixed_iff R n _).mp
  have he := contraction_natural volume (sectorMomentumCutoff R n) f q
  rw [hfix] at he
  exact he

theorem sectorAnnihilation_bounded_support (f : GW.OnePhonon) (n : ℕ)
    (u : GW.Fock.Sector (n+1)) (R : ℝ)
    (hu : ∀ᵐ K ∂GW.Fock.sectorMeasure (n+1),
      K ∉ configurationBall (n+1) R → physicalSector (n+1) u K = 0) :
    ∀ᵐ K ∂GW.Fock.sectorMeasure n,
      K ∉ configurationBall n R → physicalSector n
        (GW.Fock.sectorAnnihilation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n u) K = 0 := by
  rw [ordinarySectorAnnihilation_contraction]
  apply contraction_bounded_support
  filter_upwards [sectorCurrying_bounded_support n u R hu,
    Lp.coeFn_smul (Real.sqrt (n+1 : ℕ) : ℂ) (sectorCurrying n u)] with k hk hs
  filter_upwards [hk,
    Lp.coeFn_smul (Real.sqrt (n+1 : ℕ) : ℂ) (physicalSector n (sectorCurrying n u k))] with K hK hsmul
  intro hout
  simp only [Pi.smul_apply] at hs hsmul
  rw [hs, map_smul, hsmul, hK hout, smul_zero]

theorem creationRestriction_core_succ (f : GW.OnePhonon) (u : boundedMomentumCore) (n : ℕ) :
    creationRestriction f (coreNumberLift u) (n+1) =
      GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n
        ((u : GW.Fock.Carrier) n) := by
  rw [creationRestriction_apply, GW.Fock.ordinaryCreation_succ]
  change _ = _
  change GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n
    (numberFormEmbedding (coreNumberLift u) n) = _
  rw [coreNumberLift_embedding]

theorem annihilationRestriction_core_apply (f : GW.OnePhonon) (u : boundedMomentumCore) (n : ℕ) :
    annihilationRestriction f (coreNumberLift u) n =
      GW.Fock.sectorAnnihilation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n
        ((u : GW.Fock.Carrier) (n+1)) := by
  rw [annihilationRestriction_apply, GW.Fock.ordinaryAnnihilation_apply]
  change GW.Fock.sectorAnnihilation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n
    (numberFormEmbedding (coreNumberLift u) (n+1)) = _
  rw [coreNumberLift_embedding]

theorem annihilationRestriction_preserves_core (f : GW.OnePhonon) (u : boundedMomentumCore) :
    annihilationRestriction f (coreNumberLift u) ∈ boundedMomentumCore := by
  obtain ⟨M,R,hM,hR,hfinite,hsupport⟩ := boundedMomentumCore_support u
  apply boundedMomentumCore_mem_of_support M R hM hR
  · intro n hn
    rw [annihilationRestriction_core_apply, hfinite (n+1) (by omega), map_zero]
  · intro n
    rw [annihilationRestriction_core_apply]
    exact sectorAnnihilation_bounded_support f n _ R (hsupport (n+1))

theorem creationRestriction_preserves_core (f : GW.OnePhonon) (u : boundedMomentumCore)
    (S : ℕ) (hS : 1 ≤ S)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), (S : ℝ) < ‖k‖ → f k = 0) :
    creationRestriction f (coreNumberLift u) ∈ boundedMomentumCore := by
  obtain ⟨M,R,hM,hR,hfinite,hsupport⟩ := boundedMomentumCore_support u
  apply boundedMomentumCore_mem_of_support (M+1) (max R S) (by omega) (hR.trans (le_max_left _ _))
  · intro n hn
    cases n with
    | zero => omega
    | succ n => rw [creationRestriction_core_succ, hfinite n (by omega), map_zero]
  · intro n
    cases n with
    | zero =>
      have hz : creationRestriction f (coreNumberLift u) 0 = 0 := by
        rw [creationRestriction_apply, GW.Fock.ordinaryCreation_zero]
      rw [hz, map_zero]
      filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := GW.Fock.sectorMeasure 0)] with k hk
      intro _
      simpa only [Pi.zero_apply] using hk
    | succ n =>
      rw [creationRestriction_core_succ]
      simpa only [Nat.cast_max] using sectorCreation_bounded_support f n _ (R : ℝ) (S : ℝ) hf (hsupport n)

end Froehlich
