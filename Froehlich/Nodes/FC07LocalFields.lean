import Froehlich.Nodes.FC07Momentum
import Froehlich.Nodes.FC08
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Number and momentum slice actions as genuine global or restricted L² fields. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

def numberActionField (u : boundedMomentumCore) : Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) :=
  annihilationField (coreNumberLift (coreNumberAction u)) - annihilationField (coreNumberLift u)

theorem numberActionField_graph (u : boundedMomentumCore) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      (annihilationField (coreNumberLift u) k,numberActionField u k) ∈ GW.Fock.numberOperator.graph := by
  filter_upwards [annihilationField_number_graph u,
    Lp.coeFn_sub (annihilationField (coreNumberLift (coreNumberAction u)))
      (annihilationField (coreNumberLift u))] with k hk hsub
  have he : numberActionField u k = annihilationField (coreNumberLift (coreNumberAction u)) k -
      annihilationField (coreNumberLift u) k := hsub
  rwa [he]

def restrictedCoreField (K : Set GW.Space) (u : boundedMomentumCore) :
    Lp GW.Fock.Carrier 2 ((volume : Measure GW.Space).restrict K) :=
  LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K (annihilationField (coreNumberLift u))

theorem restrictedCoreField_ae (K : Set GW.Space) (u : boundedMomentumCore) :
    restrictedCoreField K u =ᵐ[volume.restrict K] annihilationField (coreNumberLift u) :=
  LpToLpRestrictCLM_coeFn ℂ K (annihilationField (coreNumberLift u))

def momentumScalarOperator (a : Fin 3) (k : GW.Space) : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  (k a : ℂ) • ContinuousLinearMap.id ℂ GW.Fock.Carrier

theorem momentumScalarOperator_continuous (a : Fin 3) : Continuous (momentumScalarOperator a) :=
  (Complex.continuous_ofReal.comp (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) a)).smul continuous_const

theorem momentumScalarOperator_bound (a : Fin 3) (K : Set GW.Space) (R : ℝ)
    (hR : 0 ≤ R) (hKR : ∀ k ∈ K, ‖k‖ ≤ R) (k : GW.Space) (hk : k ∈ K) :
    ‖momentumScalarOperator a k‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro z
  change ‖(k a : ℂ) • z‖ ≤ R * ‖z‖
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le k a).trans (hKR k hk)) (norm_nonneg z)

section Local
variable (a : Fin 3) (K : Set GW.Space) (hK : MeasurableSet K) (R : ℝ)
  (hR : 0 ≤ R) (hKR : ∀ k ∈ K, ‖k‖ ≤ R)

def localMomentumScalarField (u : boundedMomentumCore) : Lp GW.Fock.Carrier 2 (volume.restrict K) :=
  continuousOperatorFieldAction K hK (momentumScalarOperator a)
    (momentumScalarOperator_continuous a).continuousOn R (momentumScalarOperator_bound a K R hR hKR)
      (restrictedCoreField K u)

theorem localMomentumScalarField_ae (u : boundedMomentumCore) :
    localMomentumScalarField a K hK R hR hKR u =ᵐ[volume.restrict K]
      (fun k => (k a : ℂ) • annihilationField (coreNumberLift u) k) := by
  have h := continuousOperatorFieldAction_ae K hK (momentumScalarOperator a)
    (momentumScalarOperator_continuous a).continuousOn R (momentumScalarOperator_bound a K R hR hKR)
      (restrictedCoreField K u)
  filter_upwards [h,restrictedCoreField_ae K u] with k hk hu
  have he : localMomentumScalarField a K hK R hR hKR u k = momentumScalarOperator a k (restrictedCoreField K u k) := hk
  change localMomentumScalarField a K hK R hR hKR u k = (k a : ℂ) • annihilationField (coreNumberLift u) k
  exact he.trans (congrArg (fun z : GW.Fock.Carrier => (k a : ℂ) • z) hu)

theorem localMomentumScalarField_norm (u : boundedMomentumCore) :
    ‖localMomentumScalarField a K hK R hR hKR u‖ ≤ R * ‖restrictedCoreField K u‖ :=
  continuousOperatorFieldAction_norm K hK (momentumScalarOperator a)
    (momentumScalarOperator_continuous a).continuousOn R (momentumScalarOperator_bound a K R hR hKR)
      (restrictedCoreField K u)

def localMomentumActionField (u : boundedMomentumCore) : Lp GW.Fock.Carrier 2 (volume.restrict K) :=
  restrictedCoreField K (coreMomentumAction a u) - localMomentumScalarField a K hK R hR hKR u

theorem localMomentumActionField_ae (u : boundedMomentumCore) :
    localMomentumActionField a K hK R hR hKR u =ᵐ[volume.restrict K]
      (fun k => annihilationField (coreNumberLift (coreMomentumAction a u)) k -
        (k a : ℂ) • annihilationField (coreNumberLift u) k) := by
  filter_upwards [Lp.coeFn_sub (restrictedCoreField K (coreMomentumAction a u))
    (localMomentumScalarField a K hK R hR hKR u),restrictedCoreField_ae K (coreMomentumAction a u),
    localMomentumScalarField_ae a K hK R hR hKR u] with k hsub hfirst hsecond
  have he : localMomentumActionField a K hK R hR hKR u k =
      restrictedCoreField K (coreMomentumAction a u) k - localMomentumScalarField a K hK R hR hKR u k := hsub
  exact he.trans (congrArg₂ (fun x y : GW.Fock.Carrier => x-y) hfirst hsecond)

theorem localMomentumActionField_graph (u : boundedMomentumCore) :
    ∀ᵐ k ∂((volume : Measure GW.Space).restrict K),
      (restrictedCoreField K u k,localMomentumActionField a K hK R hR hKR u k) ∈
        (fockRealMultiplier (fun n Q => totalMomentum n Q a)).graph := by
  filter_upwards [ae_restrict_of_ae (annihilationField_momentum_graph a u),restrictedCoreField_ae K u,
    localMomentumActionField_ae a K hK R hR hKR u] with k hk hfirst hsecond
  rwa [hfirst,hsecond]

end Local
end Froehlich
