import Froehlich.Nodes.FC01Fields
import Froehlich.Nodes.FC02

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

theorem annihilationField_finite_bound_ae (x : NumberFormSpace) (M : ℕ)
    (hx : ∀ n, M < n → numberFormEmbedding x n = 0) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∀ n, M < n → (annihilationField x k) n = 0 := by
  have hz (n : ℕ) : ∀ᵐ k ∂(volume : Measure GW.Space),
      M < n → sectorCurrying n (numberFormEmbedding x (n+1)) k = 0 := by
    by_cases hn : M < n
    · have hu := hx (n+1) (by omega)
      rw [hu, map_zero]
      filter_upwards [Lp.coeFn_zero (E := GW.Fock.Sector n) (p := 2)
        (μ := (volume : Measure GW.Space))] with k hk
      intro _
      simpa only [Pi.zero_apply] using hk
    · exact Eventually.of_forall (fun _ h => (hn h).elim)
  filter_upwards [annihilationField_scaled_common_ae x, ae_all_iff.mpr hz] with k hk hz
  intro n hn
  rw [hk n, hz n hn, smul_zero]

theorem annihilationField_finiteSectorDomain_ae (x : NumberFormSpace) (M : ℕ)
    (hx : ∀ n, M < n → numberFormEmbedding x n = 0) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      annihilationField x k ∈ GW.Fock.finiteSectorDomain GW.Fock.Sector := by
  filter_upwards [annihilationField_finite_bound_ae x M hx] with k hk
  exact (GW.Fock.finiteSectorDomain_iff GW.Fock.Sector _).mpr ⟨M,hk⟩

theorem annihilationField_core_ae (u : boundedMomentumCore) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      annihilationField (coreNumberLift u) k ∈ boundedMomentumCore := by
  obtain ⟨M,R,hM,hR,hfinite,hsupport⟩ := boundedMomentumCore_support u
  have hfin : ∀ n, M < n → numberFormEmbedding (coreNumberLift u) n = 0 := by
    simpa only [coreNumberLift_embedding] using hfinite
  have hs (n : ℕ) := sectorCurrying_bounded_support n ((u : GW.Fock.Carrier) (n+1))
    (R : ℝ) (hsupport (n+1))
  have ha := annihilationField_scaled_common_ae (coreNumberLift u)
  rw [coreNumberLift_embedding] at ha
  filter_upwards [annihilationField_finite_bound_ae (coreNumberLift u) M hfin,
    ha, ae_all_iff.mpr hs] with k hf ha hs
  apply boundedMomentumCore_mem_of_support M R hM hR _ hf
  intro n
  rw [ha n, map_smul]
  filter_upwards [hs n, Lp.coeFn_smul (Real.sqrt (n+1 : ℕ) : ℂ)
    (physicalSector n (sectorCurrying n ((u : GW.Fock.Carrier) (n+1)) k))] with K hK hsmul
  intro hout
  simp only [Pi.smul_apply] at hsmul
  rw [hsmul, hK hout, smul_zero]

end Froehlich
