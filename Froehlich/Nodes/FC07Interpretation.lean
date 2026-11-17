import Froehlich.Nodes.FC07CCR
import Froehlich.Nodes.FC07CoreSlices

/-! The bounded field CCR represents the actual maximal smeared operators
on almost every slice. Particle cutoffs exhaust all finite-sector vectors. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

theorem lowSectorProjection_eq_of_bound (M : ℕ) (u : GW.Fock.Carrier)
    (hu : ∀ n, M < n → u n = 0) : lowSectorProjection M u = u := by
  apply lp.ext
  funext n
  change GW.Fock.cutoff GW.Fock.Sector M u n = _
  rw [GW.Fock.cutoff_apply]
  by_cases hn : n ≤ M
  · rw [if_pos hn]
  · rw [if_neg hn,hu n (lt_of_not_ge hn)]

theorem finiteRootLift_field_bound (M : ℕ) (u : GW.Fock.Carrier) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∀ n, M < n →
      (annihilationField (finiteRootLift M u) k) n = 0 := by
  apply annihilationField_finite_bound_ae
  intro n hn
  rw [finiteRootLift_embedding]
  change GW.Fock.cutoff GW.Fock.Sector M u n = 0
  rw [GW.Fock.cutoff_apply,if_neg (not_le.mpr hn)]

theorem finite_field_creation_actual_CCR (M : ℕ) (f : GW.OnePhonon) (u : GW.Fock.Carrier) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      (annihilationField (finiteRootLift M u) k,
        finiteCreationMap M f (annihilationField (finiteRootLift M u) k)) ∈
          (GW.Fock.ordinaryCreation f).graph ∧
      annihilationField (finiteRootLift (M+1) (finiteCreationMap M f u)) k =
        finiteCreationMap M f (annihilationField (finiteRootLift M u) k) +
          f k • lowSectorProjection M u := by
  filter_upwards [finiteRootLift_field_bound M u,
    GW.Fock.amplify_ae volume (finiteCreationMap M f) (annihilationField (finiteRootLift M u)),
    GW.Fock.tensorEmbedding_ae volume f (lowSectorProjection M u),
    Lp.coeFn_add
      (GW.Fock.amplify volume (finiteCreationMap M f) (annihilationField (finiteRootLift M u)))
      (GW.Fock.tensorEmbedding volume f (lowSectorProjection M u))] with k hbound hamp htensor hadd
  constructor
  · have hg := finiteCreationMap_graph M f (annihilationField (finiteRootLift M u) k)
    rwa [lowSectorProjection_eq_of_bound M _ hbound] at hg
  · have he := congrArg (fun q : Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) => q k)
      (finite_field_creation_CCR M f u)
    simp only [Pi.add_apply] at hadd
    rw [hadd,hamp,htensor] at he
    exact he

theorem finite_field_annihilation_actual_CCR (M : ℕ) (f : GW.OnePhonon) (u : GW.Fock.Carrier) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      (annihilationField (finiteRootLift M u) k,
        finiteAnnihilationMap M f (annihilationField (finiteRootLift M u) k)) ∈
          (GW.Fock.ordinaryAnnihilation f).graph ∧
      annihilationField (finiteRootLift M (finiteAnnihilationMap M f u)) k =
        finiteAnnihilationMap M f (annihilationField (finiteRootLift M u) k) := by
  filter_upwards [finiteRootLift_field_bound M u,
    GW.Fock.amplify_ae volume (finiteAnnihilationMap M f) (annihilationField (finiteRootLift M u))]
      with k hbound hamp
  constructor
  · have hg := finiteAnnihilationMap_graph M f (annihilationField (finiteRootLift M u) k)
    rwa [lowSectorProjection_eq_of_bound M _ hbound] at hg
  · have he := congrArg (fun q : Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) => q k)
      (finite_field_annihilation_CCR M f u)
    exact he.trans hamp

/-- Every finite-sector input has one of the exact cutoff lifts above. -/
theorem finiteNumberLift_eq_some_cutoff (u : GW.Fock.finiteSectorDomain GW.Fock.Sector) :
    ∃ M : ℕ, finiteRootLift M (u : GW.Fock.Carrier) = finiteNumberLift u := by
  obtain ⟨M,hM⟩ := (GW.Fock.finiteSectorDomain_iff GW.Fock.Sector (u : GW.Fock.Carrier)).mp u.property
  refine ⟨M,?_⟩
  apply numberFormEmbedding_injective
  rw [finiteRootLift_embedding,finiteNumberLift_embedding]
  exact lowSectorProjection_eq_of_bound M _ hM

end Froehlich
