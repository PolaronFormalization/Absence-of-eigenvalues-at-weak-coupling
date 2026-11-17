import Froehlich.Nodes.SY01Annihilation
import Froehlich.Nodes.FC06

/-! Creation covariance follows from the actual adjoint pairing and dense
physical number-graph embedding. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

theorem ambientConjugation_inner (n : ℕ) (u v : GW.Fock.AmbientSector n) :
    ⟪ambientConjugation n u,ambientConjugation n v⟫_ℂ = (starRingEnd ℂ) ⟪u,v⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [ambientConjugation_ae n u, ambientConjugation_ae n v] with k hu hv
  rw [hu,hv]
  simp only [RCLike.inner_apply', map_mul, starRingEnd_self_apply]

theorem sectorConjugation_inner (n : ℕ) (u v : GW.Fock.Sector n) :
    ⟪sectorConjugation n u,sectorConjugation n v⟫_ℂ = (starRingEnd ℂ) ⟪u,v⟫_ℂ := by
  rw [← (physicalSector n).inner_map_map, sectorConjugation_physical,
    sectorConjugation_physical, ambientConjugation_inner, LinearIsometry.inner_map_map]

theorem fockConjugation_inner (u v : GW.Fock.Carrier) :
    ⟪fockConjugation u,fockConjugation v⟫_ℂ = (starRingEnd ℂ) ⟪u,v⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  calc
    _ = ∑' n : ℕ, (starRingEnd ℂ) ⟪u n,v n⟫_ℂ :=
      tsum_congr (fun n => sectorConjugation_inner n (u n) (v n))
    _ = _ := by
      have he : (starRingEnd ℂ) (∑' n : ℕ, ⟪u n,v n⟫_ℂ) =
          ∑' n : ℕ, (starRingEnd ℂ) ⟪u n,v n⟫_ℂ := Complex.conjCLE.map_tsum
      exact he.symm

theorem creationRestriction_conjugation (f : GW.OnePhonon) (x : NumberFormSpace) :
    creationRestriction (conjugateOnePhonon f) (numberConjugation x) =
      fockConjugation (creationRestriction f x) := by
  have ht (w : NumberFormSpace) :
      ⟪creationRestriction (conjugateOnePhonon f) (numberConjugation x),
        numberFormEmbedding (numberConjugation w)⟫_ℂ =
      ⟪fockConjugation (creationRestriction f x),numberFormEmbedding (numberConjugation w)⟫_ℂ := by
    rw [smeared_adjoint_pairing, numberConjugation_intertwines, numberConjugation_intertwines,
      annihilationRestriction_conjugation, fockConjugation_inner,
      fockConjugation_inner, smeared_adjoint_pairing]
  apply ext_inner_right ℂ
  intro z
  exact numberFormEmbedding_dense.induction_on z
    (isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id))
    (fun w => by simpa only [numberConjugation_involutive w] using ht (numberConjugation w))

theorem creationRestriction_reflection (f : GW.OnePhonon) (x : NumberFormSpace) :
    creationRestriction (reflectOnePhonon f) (numberReflection x) =
      fockReflection (creationRestriction f x) := by
  have ht (w : NumberFormSpace) :
      ⟪creationRestriction (reflectOnePhonon f) (numberReflection x),
        numberFormEmbedding (numberReflection w)⟫_ℂ =
      ⟪fockReflection (creationRestriction f x),numberFormEmbedding (numberReflection w)⟫_ℂ := by
    rw [smeared_adjoint_pairing, numberReflection_intertwines, numberReflection_intertwines,
      annihilationRestriction_reflection]
    change ⟪fockReflectionEquiv (numberFormEmbedding x),
        fockReflectionEquiv (annihilationRestriction f w)⟫_ℂ =
      ⟪fockReflectionEquiv (creationRestriction f x),fockReflectionEquiv (numberFormEmbedding w)⟫_ℂ
    rw [LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map, smeared_adjoint_pairing]
  apply ext_inner_right ℂ
  intro z
  exact numberFormEmbedding_dense.induction_on z
    (isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id))
    (fun w => by simpa only [numberReflection_involutive w] using ht (numberReflection w))

end Froehlich
