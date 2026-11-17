import Froehlich.Nodes.FC07CCR
import Froehlich.Nodes.FC01Polynomials

/-! Actual number and momentum commutations on the bounded-coordinate core. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

def coreNumberInput (u : boundedMomentumCore) : GW.Fock.numberOperator.domain :=
  ⟨u,core_mem_numberOperator_domain u.property⟩

def coreNumberAction (u : boundedMomentumCore) : boundedMomentumCore :=
  ⟨GW.Fock.numberOperator (coreNumberInput u),numberOperator_preserves_core _ u.property⟩

theorem coreNumberAction_apply (u : boundedMomentumCore) (n : ℕ) :
    (coreNumberAction u : GW.Fock.Carrier) n = (n : ℂ) • (u : GW.Fock.Carrier) n :=
  GW.Fock.numberDiagonal_apply GW.Fock.Sector (coreNumberInput u) n

/-- Retained number pullthrough is available on each genuine core input. -/
def coreThreeHalfInput (u : boundedMomentumCore) :
    (GW.Fock.shiftedNumberPower GW.Fock.Sector (3/2)).domain :=
  ⟨u,GW.Fock.finiteSectorDomain_le GW.Fock.Sector (fun n => ((n : ℝ)+1)^(3/2 : ℝ))
    (boundedMomentumCore_le_finiteSector u.property)⟩

theorem core_retained_number_pullthrough (f : GW.OnePhonon) (u : boundedMomentumCore) :
    GW.Fock.ordinaryAnnihilation f (GW.Fock.pullthroughAnnihilationNumberInput f (coreThreeHalfInput u)) =
      GW.Fock.numberOperator (GW.Fock.pullthroughShiftedNumberInput
        (GW.Fock.pullthroughAnnihilationOutput f (coreThreeHalfInput u))) +
        (GW.Fock.pullthroughAnnihilationOutput f (coreThreeHalfInput u)).val :=
  GW.Fock.ordinary_annihilation_number_pullthrough_plus f (coreThreeHalfInput u)

theorem annihilationField_number_components (u : boundedMomentumCore) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∀ n,
      (annihilationField (coreNumberLift (coreNumberAction u)) k) n =
        ((n+1 : ℕ) : ℂ) • (annihilationField (coreNumberLift u) k) n := by
  have hlinear (n : ℕ) :
      sectorCurrying n ((coreNumberAction u : GW.Fock.Carrier) (n+1)) =
        ((n+1 : ℕ) : ℂ) • sectorCurrying n ((u : GW.Fock.Carrier) (n+1)) := by
    rw [coreNumberAction_apply, map_smul]
  have hcoe (n : ℕ) := Lp.coeFn_smul ((n+1 : ℕ) : ℂ)
    (sectorCurrying n ((u : GW.Fock.Carrier) (n+1)))
  have hN := annihilationField_scaled_common_ae (coreNumberLift (coreNumberAction u))
  have hU := annihilationField_scaled_common_ae (coreNumberLift u)
  rw [coreNumberLift_embedding] at hN hU
  filter_upwards [hN,hU,ae_all_iff.mpr hcoe] with k hkN hkU hkcoe
  intro n
  rw [hkN n,hkU n,hlinear n,hkcoe n]
  simp only [Pi.smul_apply]
  exact smul_comm _ _ _

/-- A N u = (N+1) A u, expressed as membership in the actual retained
number graph; the vector-valued difference is itself an L² field. -/
theorem annihilationField_number_graph (u : boundedMomentumCore) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      (annihilationField (coreNumberLift u) k,
        annihilationField (coreNumberLift (coreNumberAction u)) k -
          annihilationField (coreNumberLift u) k) ∈ GW.Fock.numberOperator.graph := by
  filter_upwards [annihilationField_number_components u] with k hk
  apply (GW.Fock.scalarDiagonal_graph_iff GW.Fock.Sector (fun n => (n : ℝ)) _).mpr
  intro n
  change (annihilationField (coreNumberLift (coreNumberAction u)) k) n -
      (annihilationField (coreNumberLift u) k) n = (n : ℂ) • (annihilationField (coreNumberLift u) k) n
  rw [hk n]
  simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul, add_sub_cancel_right]

end Froehlich
