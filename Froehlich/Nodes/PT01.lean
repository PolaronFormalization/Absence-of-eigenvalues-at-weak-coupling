import Froehlich.Nodes.PT01RegularSourceGlobal
import Froehlich.Nodes.PT01CoreCutoffGlobal
import Froehlich.Nodes.RS01

set_option autoImplicit false

/-! PT01 / lem:pullthrough. The source index n is m+1, hence n=1 or 2.
An arbitrary bounded measurable K is represented by any nonnegative radius
bounding its norm. NumberFormSpace is the genuine complete number domain.
All inverses, including every cutoff inverse, use the same fixed e. -/
noncomputable section
open MeasureTheory
namespace Froehlich

def PT01FixedReference (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) : Prop :=
  ∀ (m : ℕ) (hm : m+1 ≤ 2) (p : GW.Space) (F : NumberFormSpace)
    (hF : numberFormEmbedding F ∈ HighSectorSpace (m+1)),
    numberFormEmbedding
      (ptRegularSingularNumberVector (m+1) e p hm he g hg hs ⟨numberFormEmbedding F,hF⟩) =
      (auxiliaryResolvent (m+1) e p he g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier) ∧
    (∀ (K : Set GW.Space) (hK : MeasurableSet K) (R : ℝ) (hR : 0 ≤ R)
      (hKR : ∀ k ∈ K, ‖k‖ ≤ R),
      LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K
        (annihilationField (ptRegularSingularNumberVector (m+1) e p hm he g hg hs ⟨numberFormEmbedding F,hF⟩)) =
        (HighSectorSpace m).subtypeL.compLp
          (localSingularInverseField m e p ((Nat.le_succ m).trans hm) he g hg hs K hK
            (ptCoreLocal_isBounded K R hKR)
            (localPullthroughSource m K F
              (highSectorProject m
                (auxiliaryResolvent (m+1) e p he g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier))
              (fun k => (fiberFormFactor g k : ℂ)) (regularSource_local_formFactor_memLp g K hK R hKR)))) ∧
    (∀ᵐ k ∂volume, ∃ q : HighSectorSpace m,
      (q : GW.Fock.Carrier) = annihilationField F k - (fiberFormFactor g k : ℂ) •
        (auxiliaryResolvent (m+1) e p he g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier) ∧
      annihilationField (ptRegularSingularNumberVector (m+1) e p hm he g hg hs ⟨numberFormEmbedding F,hF⟩) k =
        (auxiliaryResolvent m e (p+k) he g hg hs q : GW.Fock.Carrier)) ∧
    ∀ Λ : GW.Operators.PositiveCutoff,
      numberFormEmbedding (freeGraphNumberCoordinates (-p)
        (cutoffAuxiliaryGraphCoordinate (m+1) e p hm he Λ g hg hs ⟨numberFormEmbedding F,hF⟩)) =
        (cutoffAuxiliaryResolvent (m+1) e p he Λ g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier) ∧
      (∀ (K : Set GW.Space) (hK : MeasurableSet K) (R : ℝ) (hR : 0 ≤ R)
        (hKR : ∀ k ∈ K, ‖k‖ ≤ R),
        LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K
          (annihilationField (freeGraphNumberCoordinates (-p)
            (cutoffAuxiliaryGraphCoordinate (m+1) e p hm he Λ g hg hs ⟨numberFormEmbedding F,hF⟩))) =
          (HighSectorSpace m).subtypeL.compLp
            (localCutoffInverseField m e p ((Nat.le_succ m).trans hm) he g hg hs K hK Λ
              (cutoffPullthroughSource m e p he Λ g hg hs K F hF))) ∧
      (∀ᵐ k ∂volume, ∃ q : HighSectorSpace m,
        (q : GW.Fock.Carrier) = annihilationField F k - (cutoffFormFactor g Λ.val k : ℂ) •
          (cutoffAuxiliaryResolvent (m+1) e p he Λ g hg hs ⟨numberFormEmbedding F,hF⟩ : GW.Fock.Carrier) ∧
        annihilationField (freeGraphNumberCoordinates (-p)
          (cutoffAuxiliaryGraphCoordinate (m+1) e p hm he Λ g hg hs ⟨numberFormEmbedding F,hF⟩)) k =
          (cutoffAuxiliaryResolvent m e (p+k) he Λ g hg hs q : GW.Fock.Carrier))

theorem pt01_bounded_set_radius (K : Set GW.Space) (hK : Bornology.IsBounded K) :
    ∃ R : ℝ, 0 < R ∧ ∀ k ∈ K, ‖k‖ ≤ R := by
  obtain ⟨R,hR,hsub⟩ := hK.subset_closedBall_lt 0 (0 : GW.Space)
  refine ⟨R,hR,?_⟩
  intro k hk
  simpa only [Metric.mem_closedBall,dist_zero_right] using hsub hk

theorem finalPT01_uniform (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) :
    PT01FixedReference e he g hg hs := by
  intro m hm p F hF
  refine ⟨ptRegularSingularNumberVector_physical (m+1) e p hm he g hg hs ⟨numberFormEmbedding F,hF⟩,
    ?_,uncutPullthrough_global_source_domain m e p hm he g hg hs F hF,?_⟩
  · intro K hK R hR hKR
    exact uncutPullthrough_local m e p hm he g hg hs K hK R hR hKR F hF
  · intro Λ
    refine ⟨?_,?_,cutoffPullthrough_global_source_domain m e p hm he Λ g hg hs F hF⟩
    · exact (freeGraphNumberCoordinates_embedding (-p) _).trans
        (cutoffAuxiliaryGraphCoordinate_physical (m+1) e p hm he Λ g hg hs ⟨numberFormEmbedding F,hF⟩)
    · intro K hK R hR hKR
      exact cutoffPullthrough_local m e p hm he Λ g hg hs K hK R hR hKR F hF

theorem finalPT01 : ∃ s : ℝ, 0 < s ∧ ∀ g : ℝ, |g| < s →
    ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
    ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
      PT01FixedReference (groundEnergy (fiberHamiltonian g 0)) he g hg hs := by
  obtain ⟨s,hs,hGround⟩ := auxiliarySelfEnergy_zero_groundEnergy
  refine ⟨s,hs,?_⟩
  intro g hgSmall
  obtain ⟨he,hg,hsmall,_⟩ := hGround g hgSmall
  exact ⟨he,hg,hsmall,finalPT01_uniform _ he g hg hsmall⟩

end Froehlich
