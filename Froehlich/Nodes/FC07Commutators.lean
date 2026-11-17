import Froehlich.Nodes.FC07Momentum
import Froehlich.Nodes.FD02MultiplierSymmetry
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! Smeared momentum commutators on actual maximal domains. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

theorem closedSubmodule_integral_mem {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure X) (S : Submodule ℂ E) (hS : IsClosed (S : Set E))
    (f : X → E) (hf : Integrable f μ) (hm : ∀ᵐ x ∂μ, f x ∈ S) :
    (∫ x, f x ∂μ) ∈ S := by
  letI : IsClosed (S : Set E) := hS
  have hz : (∫ x, S.mkQL (f x) ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hm] with x hx
    exact (Submodule.Quotient.mk_eq_zero S).mpr hx
  rw [S.mkQL.integral_comp_comm hf] at hz
  exact (Submodule.Quotient.mk_eq_zero S).mp hz

theorem closedGraph_integral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (T : GW.Fock.Carrier →ₗ.[ℂ] GW.Fock.Carrier) (hT : T.IsClosed)
    (u v : X → GW.Fock.Carrier) (hu : Integrable u μ) (hv : Integrable v μ)
    (hgraph : ∀ᵐ x ∂μ, (u x,v x) ∈ T.graph) :
    ((∫ x, u x ∂μ),(∫ x, v x ∂μ)) ∈ T.graph := by
  have h := closedSubmodule_integral_mem μ T.graph hT (fun x => (u x,v x)) (hu.prodMk hv) hgraph
  have he : (∫ x, (u x,v x) ∂μ) = ((∫ x, u x ∂μ),(∫ x, v x ∂μ)) := integral_pair hu hv
  exact Eq.mp (congrArg (fun z => z ∈ T.graph) he) h

def momentumSmearingCoefficient (a : Fin 3) (S : ℕ) (k : GW.Space) : ℂ := by
  classical
  exact if ‖k‖ ≤ (S : ℝ) then (k a : ℂ) else 0

theorem momentumSmearingCoefficient_measurable (a : Fin 3) (S : ℕ) :
    Measurable (momentumSmearingCoefficient a S) := by
  classical
  apply Measurable.ite (measurableSet_le measurable_norm measurable_const)
  · exact Complex.continuous_ofReal.measurable.comp
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) a).measurable
  · exact measurable_const

theorem momentumSmearingCoefficient_bound (a : Fin 3) (S : ℕ) (k : GW.Space) :
    ‖momentumSmearingCoefficient a S k‖ ≤ (S : ℝ) := by
  classical
  unfold momentumSmearingCoefficient
  split_ifs with hk
  · simpa only [Complex.norm_real,Real.norm_eq_abs] using (PiLp.norm_apply_le k a).trans hk
  · simpa only [norm_zero] using (Nat.cast_nonneg S : (0 : ℝ) ≤ S)

def momentumSmearing (a : Fin 3) (S : ℕ) (f : GW.OnePhonon) : GW.OnePhonon :=
  GW.Analysis.boundedMultiplier (momentumSmearingCoefficient a S)
    (momentumSmearingCoefficient_measurable a S)
    (Eventually.of_forall (momentumSmearingCoefficient_bound a S)) f

theorem momentumSmearing_ae (a : Fin 3) (S : ℕ) (f : GW.OnePhonon)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), (S : ℝ) < ‖k‖ → f k = 0) :
    momentumSmearing a S f =ᵐ[volume] (fun k => (k a : ℂ) * f k) := by
  classical
  have h := GW.Analysis.boundedMultiplier_ae (momentumSmearingCoefficient a S)
    (momentumSmearingCoefficient_measurable a S)
    (Eventually.of_forall (momentumSmearingCoefficient_bound a S)) f
  filter_upwards [h,hf] with k hk hzero
  have he : momentumSmearing a S f k = momentumSmearingCoefficient a S k • f k := hk.symm
  rw [he]
  change momentumSmearingCoefficient a S k * f k = _
  unfold momentumSmearingCoefficient
  by_cases hnorm : ‖k‖ ≤ (S : ℝ)
  · rw [if_pos hnorm]
  · rw [if_neg hnorm,hzero (lt_of_not_ge hnorm),mul_zero,mul_zero]

def coreAnnihilationAction (f : GW.OnePhonon) (u : boundedMomentumCore) : boundedMomentumCore :=
  ⟨annihilationRestriction f (coreNumberLift u),annihilationRestriction_preserves_core f u⟩

theorem annihilation_momentum_graph (a : Fin 3) (S : ℕ) (f : GW.OnePhonon)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), (S : ℝ) < ‖k‖ → f k = 0)
    (u : boundedMomentumCore) :
    (annihilationRestriction f (coreNumberLift u),
      annihilationRestriction f (coreNumberLift (coreMomentumAction a u)) -
        annihilationRestriction (momentumSmearing a S f) (coreNumberLift u)) ∈
      (fockRealMultiplier (fun n K => totalMomentum n K a)).graph := by
  let T := fockRealMultiplier (fun n K => totalMomentum n K a)
  have hT : T.IsClosed := fockRealMultiplier_closed _ (fun n =>
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) a).measurable.comp (totalMomentum_measurable n))
  let A := annihilationField (coreNumberLift u)
  let B := annihilationField (coreNumberLift (coreMomentumAction a u))
  let mf := momentumSmearing a S f
  have hiA := annihilationRestriction_integrable f (coreNumberLift u)
  have hiB := annihilationRestriction_integrable f (coreNumberLift (coreMomentumAction a u))
  have hiM := annihilationRestriction_integrable mf (coreNumberLift u)
  have hpair : ∀ᵐ k ∂(volume : Measure GW.Space),
      ((starRingEnd ℂ) (f k) • A k,
        (starRingEnd ℂ) (f k) • B k - (starRingEnd ℂ) (mf k) • A k) ∈ T.graph := by
    filter_upwards [annihilationField_momentum_graph a u,momentumSmearing_ae a S f hf] with k hk hmf
    have hsm := T.graph.smul_mem ((starRingEnd ℂ) (f k)) hk
    have he : (starRingEnd ℂ) (f k) • (B k - (k a : ℂ) • A k) =
        (starRingEnd ℂ) (f k) • B k - (starRingEnd ℂ) (mf k) • A k := by
      have hstar : (starRingEnd ℂ) (mf k) = (k a : ℂ) * (starRingEnd ℂ) (f k) := by
        dsimp [mf]
        rw [hmf,map_mul,Complex.conj_ofReal]
      have hscalar : (starRingEnd ℂ) (f k) • ((k a : ℂ) • (A k : GW.Fock.Carrier)) =
          (starRingEnd ℂ) (mf k) • A k :=
        (smul_smul ((starRingEnd ℂ) (f k)) (k a : ℂ) (A k)).trans
          (congrArg (fun c : ℂ => c • (A k : GW.Fock.Carrier))
            ((mul_comm ((starRingEnd ℂ) (f k)) (k a : ℂ)).trans hstar.symm))
      exact (smul_sub ((starRingEnd ℂ) (f k)) (B k) ((k a : ℂ) • A k)).trans
        (congrArg (fun z : GW.Fock.Carrier => (starRingEnd ℂ) (f k) • B k - z) hscalar)
    change ((starRingEnd ℂ) (f k) • A k,
      (starRingEnd ℂ) (f k) • (B k - (k a : ℂ) • A k)) ∈ T.graph at hsm
    rwa [he] at hsm
  have hi := closedGraph_integral volume T hT _ _ hiA (hiB.sub hiM) hpair
  change ((∫ k, (starRingEnd ℂ) (f k) • annihilationField (coreNumberLift u) k),
    (∫ k, (starRingEnd ℂ) (f k) • annihilationField (coreNumberLift (coreMomentumAction a u)) k -
      (starRingEnd ℂ) (mf k) • annihilationField (coreNumberLift u) k)) ∈ T.graph at hi
  rw [integral_sub hiB hiM] at hi
  change ((∫ k, (starRingEnd ℂ) (f k) • annihilationField (coreNumberLift u) k),
    (∫ k, (starRingEnd ℂ) (f k) • annihilationField (coreNumberLift (coreMomentumAction a u)) k) -
      (∫ k, (starRingEnd ℂ) (momentumSmearing a S f k) • annihilationField (coreNumberLift u) k)) ∈ T.graph at hi
  rw [← annihilationRestriction_integral,← annihilationRestriction_integral,← annihilationRestriction_integral] at hi
  exact hi

theorem annihilation_momentum_action (a : Fin 3) (S : ℕ) (f : GW.OnePhonon)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), (S : ℝ) < ‖k‖ → f k = 0)
    (u : boundedMomentumCore) :
    (coreMomentumAction a (coreAnnihilationAction f u) : GW.Fock.Carrier) =
      annihilationRestriction f (coreNumberLift (coreMomentumAction a u)) -
        annihilationRestriction (momentumSmearing a S f) (coreNumberLift u) :=
  (fockRealMultiplier _).mem_graph_snd_inj
    (coreMomentumAction_graph a (coreAnnihilationAction f u))
    (annihilation_momentum_graph a S f hf u) rfl

theorem annihilation_momentum_commutator (a : Fin 3) (S : ℕ) (f : GW.OnePhonon)
    (hf : ∀ᵐ k ∂(volume : Measure GW.Space), (S : ℝ) < ‖k‖ → f k = 0)
    (u : boundedMomentumCore) :
    (coreMomentumAction a (coreAnnihilationAction f u) : GW.Fock.Carrier) -
      annihilationRestriction f (coreNumberLift (coreMomentumAction a u)) =
        -annihilationRestriction (momentumSmearing a S f) (coreNumberLift u) := by
  rw [annihilation_momentum_action a S f hf u]
  abel

end Froehlich
