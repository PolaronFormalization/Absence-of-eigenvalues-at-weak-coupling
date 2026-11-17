import Froehlich.Nodes.PT01RegularSourceLimit
import Froehlich.Nodes.FC07ProjectedCore

set_option autoImplicit false

/-! Global pure representatives for the regular-source RHS. Neither the
uncut coefficient nor the source row is declared globally L2. -/
noncomputable section
open MeasureTheory
namespace Froehlich

variable (m : ℕ) (e : ℝ) (p : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (F : NumberFormSpace) (hF : numberFormEmbedding F ∈ HighSectorSpace (m+1))

def regularSourceRow (k : GW.Space) : HighSectorSpace m :=
  highSectorProject m (annihilationField F k) - (fiberFormFactor g k : ℂ) •
    highSectorProject m (auxiliaryResolvent (m+1) e p he g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier)

def regularSourceRHSRow (k : GW.Space) : GW.Fock.Carrier :=
  (auxiliaryResolvent m e (p+k) he g hg hs (regularSourceRow m e p he g hg hs F hF k) : GW.Fock.Carrier)

theorem regularSourceRow_physical_ae :
    ∀ᵐ k ∂volume, (regularSourceRow m e p he g hg hs F hF k : GW.Fock.Carrier) =
      annihilationField F k - (fiberFormFactor g k : ℂ) •
        (auxiliaryResolvent (m+1) e p he g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier) := by
  have hU : highSectorProjection m
      (auxiliaryResolvent (m+1) e p he g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier) =
      (auxiliaryResolvent (m+1) e p he g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier) :=
    (highSector_mem_iff m _).mp (highSector_mem_of_succ m _
      (auxiliaryResolvent (m+1) e p he g hg hs ⟨numberFormEmbedding F,hF⟩).property)
  filter_upwards [annihilationField_mem_high_of_number_high m F hF] with k hk
  change highSectorProjection m (annihilationField F k) - (fiberFormFactor g k : ℂ) •
    highSectorProjection m (auxiliaryResolvent (m+1) e p he g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier) = _
  rw [(highSector_mem_iff m _).mp hk,hU]

theorem localSingularInverseField_global_row_ae (hm : m+1 ≤ 2)
    (K : Set GW.Space) (hK : MeasurableSet K) (hKb : Bornology.IsBounded K)
    (R : ℝ) (hKR : ∀ k ∈ K, ‖k‖ ≤ R) :
    (HighSectorSpace m).subtypeL.compLp
      (localSingularInverseField m e p ((Nat.le_succ m).trans hm) he g hg hs K hK hKb
        (localPullthroughSource m K F
          (highSectorProject m (auxiliaryResolvent (m+1) e p he g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier))
          (fun k => (fiberFormFactor g k : ℂ)) (regularSource_local_formFactor_memLp g K hK R hKR)))
        =ᵐ[volume.restrict K] regularSourceRHSRow m e p he g hg hs F hF := by
  let U := highSectorProject m
    (auxiliaryResolvent (m+1) e p he g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier)
  let V := localPullthroughSource m K F U (fun k => (fiberFormFactor g k : ℂ))
    (regularSource_local_formFactor_memLp g K hK R hKR)
  have hinput : V =ᵐ[volume.restrict K] regularSourceRow m e p he g hg hs F hF := by
    have hU : (U : GW.Fock.Carrier) =
        (auxiliaryResolvent (m+1) e p he g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier) :=
      (highSector_mem_iff m _).mp (highSector_mem_of_succ m _
        (auxiliaryResolvent (m+1) e p he g hg hs ⟨numberFormEmbedding F,hF⟩).property)
    filter_upwards [localPullthroughSource_physical m K F hF U
        (fun k => (fiberFormFactor g k : ℂ)) (regularSource_local_formFactor_memLp g K hK R hKR),
      ae_restrict_of_ae (s := K) (regularSourceRow_physical_ae m e p he g hg hs F hF)] with k hk hr
    apply Subtype.ext
    exact hk.trans (by rw [hU]; exact hr.symm)
  let A := localSingularInverseField m e p ((Nat.le_succ m).trans hm) he g hg hs K hK hKb V
  filter_upwards [(HighSectorSpace m).subtypeL.coeFn_compLp A,
    localSingularInverseField_ae m e p ((Nat.le_succ m).trans hm) he g hg hs K hK hKb V,hinput]
    with k hi ha hv
  change (HighSectorSpace m).subtypeL.compLp A k = _
  rw [hi,ha,hv]
  rfl

end Froehlich
