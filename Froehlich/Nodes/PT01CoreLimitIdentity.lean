import Froehlich.Nodes.PT01CoreFormTesting
import Froehlich.Nodes.PT01CoreLimit
import Froehlich.Nodes.PT01HighGraphCore

/-! The complex tested core identity extends by the actual free-graph
limit. Bounded local energy fields and physical Lu are the only limits. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Froehlich

 theorem cutoff_freeGraph_test_identity (p : GW.Space) (m : ℕ) (e : ℝ) (hm : m+1 ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (Lambda : GW.Operators.PositiveCutoff)
    (K : Set GW.Space) (hK : MeasurableSet K) (R : ℝ) (hR : 0 ≤ R) (hKR : ∀ k ∈ K, ‖k‖ ≤ R)
    (hT : AEStronglyMeasurable
      (fun k : GW.Space => (cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Lambda :
        HighEnergySpace 0 m →L[ℂ] HighEnergySpace 0 m)) ((volume : Measure GW.Space).restrict K))
    (M : ℝ) (hM : ∀ k ∈ K, ‖cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Lambda‖ ≤ M)
    (x : OperatorGraphSpace (-p)) (hx : graphEmbedding (-p) x ∈ HighSectorSpace (m+1))
    (w : highEnergyTestCore 0 m) (chi : Lp ℂ 2 ((volume : Measure GW.Space).restrict K)) :
    localL2TestFunctional K chi w.val
      (operatorFieldValue K hK
        (fun k : GW.Space => (cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Lambda :
          HighEnergySpace 0 m →L[ℂ] HighEnergySpace 0 m)) hT M hM
        (restrictedHighEnergyFieldMap (-p) m K hK R hR hKR x))=
      cutoffGraphTestRHS g (-p) (m+1) Lambda e K hK chi (ptCorePhysicalTest m w) x := by
  let T : GW.Space → HighEnergySpace 0 m →L[ℂ] HighEnergySpace 0 m :=
    fun k => cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Lambda
  let A : OperatorGraphSpace (-p) →L[ℂ] ℂ := (localL2TestFunctional K chi w.val).comp
    ((operatorFieldAction K hK T hT M hM).comp (restrictedHighEnergyFieldMap (-p) m K hK R hR hKR))
  let B := cutoffGraphTestRHS g (-p) (m+1) Lambda e K hK chi (ptCorePhysicalTest m w)
  obtain ⟨xs,hcore,hxs⟩ := highFreeGraph_core_approximation (-p) (m+1) x hx
  let us : ℕ → boundedMomentumCore := fun j => ⟨graphEmbedding (-p) (xs j),(hcore j).1⟩
  have hsame (j : ℕ) : coreFreeGraphLift (-p) (us j)=xs j := by
    apply graphEmbedding_injective (-p)
    rw [coreFreeGraphLift_embedding]
  have hus (j : ℕ) : (us j : GW.Fock.Carrier) ∈ HighSectorSpace (m+1) := (hcore j).2
  have htest (j : ℕ) : A (xs j)=B (xs j) := by
    rw [←hsame j]
    have hAE := operatorFieldValue_ae K hK T hT M hM
      (restrictedHighEnergyFieldMap (-p) m K hK R hR hKR (coreFreeGraphLift (-p) (us j)))
    have hcalc : A (coreFreeGraphLift (-p) (us j))=
        ∫ k in K, (starRingEnd ℂ) (chi k)*
          ⟪w.val,cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Lambda
            (ptCoreLocalEnergyField p m K hK R hR hKR (us j) k)⟫_ℂ := by
      change localL2TestFunctional K chi w.val
        (operatorFieldValue K hK T hT M hM
          (restrictedHighEnergyFieldMap (-p) m K hK R hR hKR (coreFreeGraphLift (-p) (us j))))=_
      rw [localL2TestFunctional_integral]
      apply integral_congr_ae
      filter_upwards [hAE] with k hk
      rw [hk]
      rfl
    have hEq := (projectedCutoffCore_form_test p m e hm he g Lambda K hK R hR hKR (us j) (hus j) w chi).2
    rw [hcalc,hEq]
    exact (cutoffGraphTestRHS_core g (-p) (m+1) Lambda e K hK chi (ptCorePhysicalTest m w) (us j)).symm
  have hA : Tendsto (fun j => A (xs j)) atTop (𝓝 (A x)) := (A.continuous.tendsto x).comp hxs
  have hB : Tendsto (fun j => B (xs j)) atTop (𝓝 (B x)) := (B.continuous.tendsto x).comp hxs
  have heq : (fun j => A (xs j))=(fun j => B (xs j)) := funext htest
  rw [heq] at hA
  exact tendsto_nhds_unique hA hB

end Froehlich
