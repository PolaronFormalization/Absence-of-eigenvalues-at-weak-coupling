import Froehlich.Nodes.FC07

/-! The retained maximal CCR lifted to actual L² momentum fields. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

theorem finiteCreationMap_graph (M : ℕ) (f : GW.OnePhonon) (u : GW.Fock.Carrier) :
    (lowSectorProjection M u,finiteCreationMap M f u) ∈ (GW.Fock.ordinaryCreation f).graph := by
  have h := (GW.Fock.ordinaryCreation f).mem_graph
    (GW.Fock.ordinaryCreationRootInput f (numberFormRootInput (finiteRootLift M u)))
  change (numberFormEmbedding (finiteRootLift M u),finiteCreationMap M f u) ∈ _ at h
  rwa [finiteRootLift_embedding] at h

theorem finiteAnnihilationMap_graph (M : ℕ) (f : GW.OnePhonon) (u : GW.Fock.Carrier) :
    (lowSectorProjection M u,finiteAnnihilationMap M f u) ∈ (GW.Fock.ordinaryAnnihilation f).graph := by
  have h := (GW.Fock.ordinaryAnnihilation f).mem_graph
    (GW.Fock.ordinaryAnnihilationRootInput f (numberFormRootInput (finiteRootLift M u)))
  change (numberFormEmbedding (finiteRootLift M u),finiteAnnihilationMap M f u) ∈ _ at h
  rwa [finiteRootLift_embedding] at h

theorem finiteCreationMap_succ (M n : ℕ) (f : GW.OnePhonon) (u : GW.Fock.Carrier) :
    finiteCreationMap M f u (n+1) =
      GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n
        (lowSectorProjection M u n) := by
  change creationRestriction f (finiteRootLift M u) (n+1) = _
  rw [creationRestriction_apply, GW.Fock.ordinaryCreation_succ]
  change GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n
    (numberFormEmbedding (finiteRootLift M u) n) = _
  rw [finiteRootLift_embedding]

theorem finiteAnnihilationMap_apply (M n : ℕ) (f : GW.OnePhonon) (u : GW.Fock.Carrier) :
    finiteAnnihilationMap M f u n =
      GW.Fock.sectorAnnihilation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n
        (lowSectorProjection M u (n+1)) := by
  change annihilationRestriction f (finiteRootLift M u) n = _
  rw [annihilationRestriction_apply, GW.Fock.ordinaryAnnihilation_apply]
  change GW.Fock.sectorAnnihilation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n
    (numberFormEmbedding (finiteRootLift M u) (n+1)) = _
  rw [finiteRootLift_embedding]

theorem finiteCreationMap_cutoff (M : ℕ) (f : GW.OnePhonon) (u : GW.Fock.Carrier) :
    lowSectorProjection (M+1) (finiteCreationMap M f u) = finiteCreationMap M f u := by
  apply lp.ext
  funext n
  change GW.Fock.cutoff GW.Fock.Sector (M+1) (finiteCreationMap M f u) n = _
  rw [GW.Fock.cutoff_apply]
  by_cases hn : n ≤ M+1
  · rw [if_pos hn]
  · rw [if_neg hn]
    cases n with
    | zero => omega
    | succ n =>
      rw [finiteCreationMap_succ]
      change 0 = GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n
        (GW.Fock.cutoff GW.Fock.Sector M u n)
      rw [GW.Fock.cutoff_apply, if_neg (by omega), map_zero]

theorem finiteAnnihilationMap_cutoff (M : ℕ) (f : GW.OnePhonon) (u : GW.Fock.Carrier) :
    lowSectorProjection M (finiteAnnihilationMap M f u) = finiteAnnihilationMap M f u := by
  apply lp.ext
  funext n
  change GW.Fock.cutoff GW.Fock.Sector M (finiteAnnihilationMap M f u) n = _
  rw [GW.Fock.cutoff_apply]
  by_cases hn : n ≤ M
  · rw [if_pos hn]
  · rw [if_neg hn, finiteAnnihilationMap_apply]
    change 0 = GW.Fock.sectorAnnihilation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n
      (GW.Fock.cutoff GW.Fock.Sector M u (n+1))
    rw [GW.Fock.cutoff_apply, if_neg (by omega), map_zero]

theorem finite_maps_mixed_CCR (M : ℕ) (f g : GW.OnePhonon) (u : GW.Fock.Carrier) :
    finiteAnnihilationMap (M+1) g (finiteCreationMap M f u) =
      finiteCreationMap M f (finiteAnnihilationMap M g u) + ⟪g,f⟫_ℂ • lowSectorProjection M u := by
  let x : GW.Fock.numberOperator.domain :=
    ⟨lowSectorProjection M u,GW.Fock.scalarDiagonal_cutoff_mem GW.Fock.Sector (fun n => (n : ℝ)) M u⟩
  obtain ⟨c,a,ac,ca,hc,ha,hac,hca,he⟩ := GW.Fock.ordinaryCCR_mixed_graphs g f x
  have hc' := (GW.Fock.ordinaryCreation f).mem_graph_snd_inj hc (finiteCreationMap_graph M f u) rfl
  have ha' := (GW.Fock.ordinaryAnnihilation g).mem_graph_snd_inj ha (finiteAnnihilationMap_graph M g u) rfl
  subst c
  subst a
  have hac' := (GW.Fock.ordinaryAnnihilation g).mem_graph_snd_inj hac
    (finiteAnnihilationMap_graph (M+1) g (finiteCreationMap M f u))
    (finiteCreationMap_cutoff M f u).symm
  have hca' := (GW.Fock.ordinaryCreation f).mem_graph_snd_inj hca
    (finiteCreationMap_graph M f (finiteAnnihilationMap M g u))
    (finiteAnnihilationMap_cutoff M g u).symm
  rw [hac', hca'] at he
  have hresult : finiteAnnihilationMap (M+1) g (finiteCreationMap M f u) =
      ⟪g,f⟫_ℂ • lowSectorProjection M u + finiteCreationMap M f (finiteAnnihilationMap M g u) :=
    sub_eq_iff_eq_add.mp he
  exact hresult.trans (add_comm _ _)

theorem finite_maps_annihilation_CCR (M : ℕ) (f g : GW.OnePhonon) (u : GW.Fock.Carrier) :
    finiteAnnihilationMap M g (finiteAnnihilationMap M f u) =
      finiteAnnihilationMap M f (finiteAnnihilationMap M g u) := by
  let x : GW.Fock.numberOperator.domain :=
    ⟨lowSectorProjection M u,GW.Fock.scalarDiagonal_cutoff_mem GW.Fock.Sector (fun n => (n : ℝ)) M u⟩
  obtain ⟨a,b,ab,ba,ha,hb,hab,hba,he⟩ := GW.Fock.ordinaryCCR_annihilation_graphs g f x
  have ha' := (GW.Fock.ordinaryAnnihilation f).mem_graph_snd_inj ha (finiteAnnihilationMap_graph M f u) rfl
  have hb' := (GW.Fock.ordinaryAnnihilation g).mem_graph_snd_inj hb (finiteAnnihilationMap_graph M g u) rfl
  subst a
  subst b
  have hab' := (GW.Fock.ordinaryAnnihilation g).mem_graph_snd_inj hab
    (finiteAnnihilationMap_graph M g (finiteAnnihilationMap M f u))
    (finiteAnnihilationMap_cutoff M f u).symm
  have hba' := (GW.Fock.ordinaryAnnihilation f).mem_graph_snd_inj hba
    (finiteAnnihilationMap_graph M f (finiteAnnihilationMap M g u))
    (finiteAnnihilationMap_cutoff M g u).symm
  exact hab'.symm.trans (he.trans hba')

theorem finite_field_creation_CCR (M : ℕ) (f : GW.OnePhonon) (u : GW.Fock.Carrier) :
    annihilationField (finiteRootLift (M+1) (finiteCreationMap M f u)) =
      GW.Fock.amplify volume (finiteCreationMap M f) (annihilationField (finiteRootLift M u)) +
        GW.Fock.tensorEmbedding volume f (lowSectorProjection M u) := by
  apply fockField_ext_of_contractions
  intro g
  rw [map_add, ← contraction_natural, contraction_tensor]
  rw [← annihilationRestriction_eq_contraction, ← annihilationRestriction_eq_contraction]
  exact finite_maps_mixed_CCR M f g u

theorem finite_field_annihilation_CCR (M : ℕ) (f : GW.OnePhonon) (u : GW.Fock.Carrier) :
    annihilationField (finiteRootLift M (finiteAnnihilationMap M f u)) =
      GW.Fock.amplify volume (finiteAnnihilationMap M f) (annihilationField (finiteRootLift M u)) := by
  apply fockField_ext_of_contractions
  intro g
  rw [← contraction_natural, ← annihilationRestriction_eq_contraction,
    ← annihilationRestriction_eq_contraction]
  exact finite_maps_annihilation_CCR M f g u

end Froehlich
