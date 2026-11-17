import Froehlich.Nodes.PT01CoreLocalTesting
import Froehlich.Nodes.PT01CutoffGraph
import Froehlich.Nodes.PT01HighCoreDensity

/-! The actual projected core graph identity, expressed in the fixed
energy space and integrated against every complex local L² scalar test. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

def ptCoreLocalEnergyField (p : GW.Space) (m : ℕ) (K : Set GW.Space) (hK : MeasurableSet K)
    (R : ℝ) (hR : 0 ≤ R) (hKR : ∀ k ∈ K, ‖k‖ ≤ R) (u : boundedMomentumCore) :
    Lp (HighEnergySpace 0 m) 2 ((volume : Measure GW.Space).restrict K) :=
  restrictedHighEnergyFieldMap (-p) m K hK R hR hKR (coreFreeGraphLift (-p) u)

theorem ptCoreLocalEnergyField_physical (p : GW.Space) (m : ℕ) (K : Set GW.Space) (hK : MeasurableSet K)
    (R : ℝ) (hR : 0 ≤ R) (hKR : ∀ k ∈ K, ‖k‖ ≤ R) (u : boundedMomentumCore)
    (hu : (u : GW.Fock.Carrier) ∈ HighSectorSpace (m+1)) :
    ∀ᵐ k ∂((volume : Measure GW.Space).restrict K),
      (highEnergyEmbedding 0 m (ptCoreLocalEnergyField p m K hK R hR hKR u k) : GW.Fock.Carrier)=
        annihilationField (coreNumberLift u) k := by
  have hx : graphEmbedding (-p) (coreFreeGraphLift (-p) u) ∈ HighSectorSpace (m+1) := by
    rw [coreFreeGraphLift_embedding]
    exact hu
  have hn : freeGraphNumberCoordinates (-p) (coreFreeGraphLift (-p) u)=coreNumberLift u := by
    apply numberFormEmbedding_injective
    rw [freeGraphNumberCoordinates_embedding,coreFreeGraphLift_embedding,coreNumberLift_embedding]
  have h := restrictedHighEnergyFieldMap_physical (-p) m K hK R hR hKR (coreFreeGraphLift (-p) u) hx
  rw [hn] at h
  exact h

theorem projectedCutoffCore_fixed_form_ae (p : GW.Space) (m : ℕ) (e : ℝ) (hm : m+1 ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (Lambda : GW.Operators.PositiveCutoff)
    (K : Set GW.Space) (hK : MeasurableSet K) (R : ℝ) (hR : 0 ≤ R) (hKR : ∀ k ∈ K, ‖k‖ ≤ R)
    (u : boundedMomentumCore) (hu : (u : GW.Fock.Carrier) ∈ HighSectorSpace (m+1)) :
    ∀ᵐ k ∂((volume : Measure GW.Space).restrict K), ∀ w : HighEnergySpace 0 m,
      ⟪w,cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Lambda
        (ptCoreLocalEnergyField p m K hK R hR hKR u k)⟫_ℂ=
      ⟪(highEnergyEmbedding 0 m w : GW.Fock.Carrier),projectedCutoffShiftField g (-p) (m+1) Lambda e u k⟫_ℂ := by
  filter_upwards [ptCoreLocalEnergyField_physical p m K hK R hR hKR u hu,
    ae_restrict_of_ae (s := K) (projectedCutoffShiftField_graph g (-p) m Lambda e u hu)] with k hv hgraph
  obtain ⟨q,r,hq,hr,hgraph⟩ := hgraph
  have hp : -p-k=-(p+k) := by abel
  rw [hp] at hgraph
  have hvq : highEnergyEmbedding 0 m (ptCoreLocalEnergyField p m K hK R hR hKR u k)=q := by
    apply Subtype.ext
    exact hv.trans hq.symm
  have hpair : ∀ v : HighEnergySpace 0 m, highEnergyEmbedding 0 m v=q →
      (q,r) ∈ (GW.Operators.complexShift (compressedHamiltonian g (-(p+k)) m (some Lambda))
        ((e-1+(m : ℝ) : ℝ) : ℂ)).graph → ∀ w : HighEnergySpace 0 m,
      ⟪w,cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Lambda v⟫_ℂ=
        ⟪highEnergyEmbedding 0 m w,r⟫_ℂ := by
    simpa only [neg_zero] using! cutoffShiftGraph_fixed_pairing m e 0 (p+k)
      ((Nat.le_succ m).trans hm) he g Lambda q r
  intro w
  have h := hpair _ hvq hgraph w
  change ⟪w,cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Lambda
    (ptCoreLocalEnergyField p m K hK R hR hKR u k)⟫_ℂ=
      ⟪(highEnergyEmbedding 0 m w : GW.Fock.Carrier),(r : GW.Fock.Carrier)⟫_ℂ at h
  rw [hr] at h
  exact h

def ptCorePhysicalTest (m : ℕ) (w : highEnergyTestCore 0 m) : boundedMomentumCore :=
  ⟨energyEmbedding 0 (w.val : EnergySpace 0),w.property⟩

theorem projectedCutoffCore_form_test (p : GW.Space) (m : ℕ) (e : ℝ) (hm : m+1 ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (Lambda : GW.Operators.PositiveCutoff)
    (K : Set GW.Space) (hK : MeasurableSet K) (R : ℝ) (hR : 0 ≤ R) (hKR : ∀ k ∈ K, ‖k‖ ≤ R)
    (u : boundedMomentumCore) (hu : (u : GW.Fock.Carrier) ∈ HighSectorSpace (m+1))
    (w : highEnergyTestCore 0 m) (chi : Lp ℂ 2 ((volume : Measure GW.Space).restrict K)) :
    Integrable (fun k => (starRingEnd ℂ) (chi k)*
      ⟪w.val,cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Lambda
        (ptCoreLocalEnergyField p m K hK R hR hKR u k)⟫_ℂ) ((volume : Measure GW.Space).restrict K) ∧
    (∫ k in K, (starRingEnd ℂ) (chi k)*
      ⟪w.val,cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Lambda
        (ptCoreLocalEnergyField p m K hK R hR hKR u k)⟫_ℂ)=
      ⟪creationRestriction (localScalarTestExtension K hK chi) (coreNumberLift (ptCorePhysicalTest m w)),
        (coreProjectedCutoffShiftAction g (-p) (m+1) Lambda e u : GW.Fock.Carrier)⟫_ℂ-
      ∫ k in K, ((starRingEnd ℂ) (chi k)*cutoffFormFactorL2 g Lambda.val Lambda.property k)*
        ⟪(ptCorePhysicalTest m w : GW.Fock.Carrier),(u : GW.Fock.Carrier)⟫_ℂ := by
  obtain ⟨hi,_,heq⟩ := projectedCutoffCore_local_test g (-p) (m+1) Lambda e u (ptCorePhysicalTest m w) K hK chi
  have hscalar : (fun k => (starRingEnd ℂ) (chi k)*
      ⟪w.val,cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Lambda
        (ptCoreLocalEnergyField p m K hK R hR hKR u k)⟫_ℂ) =ᵐ[(volume : Measure GW.Space).restrict K]
      (fun k => (starRingEnd ℂ) (chi k)*⟪(ptCorePhysicalTest m w : GW.Fock.Carrier),
        projectedCutoffShiftField g (-p) (m+1) Lambda e u k⟫_ℂ) := by
    filter_upwards [projectedCutoffCore_fixed_form_ae p m e hm he g Lambda K hK R hR hKR u hu] with k hk
    rw [hk w.val]
    change (starRingEnd ℂ) (chi k)*⟪(highEnergyEmbedding 0 m w.val : GW.Fock.Carrier),_⟫_ℂ=_
    rw [highEnergyEmbedding_apply]
    rfl
  exact ⟨hi.congr hscalar.symm,(integral_congr_ae hscalar).trans heq⟩

end Froehlich
