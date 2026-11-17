import Froehlich.Nodes.FC01Multipliers

/-! The polynomial multipliers on the bounded-momentum core, with the
retained number and free operators as their actual actions. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

theorem totalMomentum_bound_on_configuration (M R n : ℕ) (hn : n ≤ M)
    (k : GW.Fock.Coordinates n) (hk : k ∈ configurationBall n (R : ℝ)) :
    ‖totalMomentum n k‖ ≤ (M : ℝ) * R := by
  calc
    ‖totalMomentum n k‖ ≤ ∑ i : Fin n, ‖k i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, (R : ℝ) := Finset.sum_le_sum (fun i _ => hk i)
    _ = (n : ℝ) * R := by simp
    _ ≤ (M : ℝ) * R := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (Nat.cast_nonneg R)

theorem freeSymbol_bound_on_configuration (P : GW.Space) (M R n : ℕ) (hn : n ≤ M)
    (k : GW.Fock.Coordinates n) (hk : k ∈ configurationBall n (R : ℝ)) :
    freeSymbol P n k ≤ ((M : ℝ) * R + ‖P‖)^2 + M := by
  have htriangle : ‖totalMomentum n k - P‖ ≤ ‖totalMomentum n k‖ + ‖P‖ :=
    norm_sub_le (totalMomentum n k) P
  have hadd : ‖totalMomentum n k‖ + ‖P‖ ≤ (M : ℝ) * R + ‖P‖ :=
    add_le_add (totalMomentum_bound_on_configuration M R n hn k hk) (le_refl ‖P‖)
  have hnorm : ‖totalMomentum n k - P‖ ≤ (M : ℝ) * R + ‖P‖ := htriangle.trans hadd
  have hsq := sq_le_sq₀ (norm_nonneg (totalMomentum n k - P)) (by positivity : 0 ≤ (M : ℝ) * R + ‖P‖)
  have hn' : (n : ℝ) ≤ M := by exact_mod_cast hn
  exact add_le_add (hsq.mpr hnorm) hn'

theorem core_free_multiplier_graph (P : GW.Space) (u : boundedMomentumCore) :
    ∃ v : GW.Fock.Carrier, v ∈ boundedMomentumCore ∧
      ((u : GW.Fock.Carrier),v) ∈ (freeFiberOperator P).graph := by
  rw [freeFiberOperator_eq_fockRealMultiplier]
  apply core_multiplier_graph_exists (freeSymbol P) (freeSymbol_measurable P) (freeSymbol_permutation P)
  intro M R
  refine ⟨((M : ℝ) * R + ‖P‖)^2 + M, by positivity, ?_⟩
  intro n hn k hk
  rw [abs_of_nonneg (freeSymbol_nonneg P n k)]
  exact freeSymbol_bound_on_configuration P M R n hn k hk

theorem core_mem_freeFiberOperator_domain (P : GW.Space) :
    boundedMomentumCore ≤ (freeFiberOperator P).domain := by
  intro u hu
  obtain ⟨v,hv,hg⟩ := core_free_multiplier_graph P ⟨u,hu⟩
  exact (freeFiberOperator P).mem_domain_of_mem_graph hg

theorem freeFiberOperator_preserves_core (P : GW.Space) (u : (freeFiberOperator P).domain)
    (hu : (u : GW.Fock.Carrier) ∈ boundedMomentumCore) :
    freeFiberOperator P u ∈ boundedMomentumCore := by
  apply multiplier_graph_preserves_core (freeSymbol P) ⟨u,hu⟩
  rw [← freeFiberOperator_eq_fockRealMultiplier]
  exact (freeFiberOperator P).mem_graph u

theorem core_mem_energyEmbedding_range (P : GW.Space) (u : boundedMomentumCore) :
    (u : GW.Fock.Carrier) ∈ Set.range (energyEmbedding P) := by
  obtain ⟨v,hv,hg⟩ := core_free_multiplier_graph P u
  exact ⟨(energyEmbedding P).adjoint (v + (u : GW.Fock.Carrier)),
    freeFiberOperator_graph_energyLift P _ _ hg⟩

theorem core_mem_energyWeightOperator_domain (P : GW.Space) :
    boundedMomentumCore ≤ (energyWeightOperator P).domain := by
  intro u hu
  have h := core_mem_energyEmbedding_range P ⟨u,hu⟩
  rwa [energyEmbedding_range] at h

theorem core_energyWeight_multiplier_graph (P : GW.Space) (u : boundedMomentumCore) :
    ∃ v : GW.Fock.Carrier, v ∈ boundedMomentumCore ∧
      ((u : GW.Fock.Carrier),v) ∈ (fockRealMultiplier (energyWeight P)).graph := by
  apply core_multiplier_graph_exists (energyWeight P) (energyWeight_measurable P) (energyWeight_permutation P)
  intro M R
  let C : ℝ := ((M : ℝ) * R + ‖P‖)^2 + M
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨1+C, by positivity, ?_⟩
  intro n hn k hk
  rw [abs_of_nonneg ((zero_lt_one.trans_le (energyWeight_ge_one P n k)).le)]
  change Real.sqrt (1 + freeSymbol P n k) ≤ 1+C
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hF : freeSymbol P n k ≤ C := freeSymbol_bound_on_configuration P M R n hn k hk
  nlinarith [sq_nonneg C]

theorem core_momentum_component_graph (a : Fin 3) (u : boundedMomentumCore) :
    ∃ v : GW.Fock.Carrier, v ∈ boundedMomentumCore ∧
      ((u : GW.Fock.Carrier),v) ∈ (fockRealMultiplier (fun n k => totalMomentum n k a)).graph := by
  apply core_multiplier_graph_exists (fun n k => totalMomentum n k a)
  · intro n
    exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) a).measurable.comp (totalMomentum_measurable n)
  · intro n τ k
    rw [totalMomentum_permutation]
  · intro M R
    refine ⟨(M : ℝ) * R, by positivity, ?_⟩
    intro n hn k hk
    exact (PiLp.norm_apply_le (totalMomentum n k) a).trans
      (totalMomentum_bound_on_configuration M R n hn k hk)

theorem core_mem_numberOperator_domain : boundedMomentumCore ≤ GW.Fock.numberOperator.domain := by
  intro u hu
  exact GW.Fock.finiteSectorDomain_le GW.Fock.Sector (fun n => (n : ℝ))
    (boundedMomentumCore_le_finiteSector hu)

theorem retainedNumber_graph_is_multiplier (u : GW.Fock.numberOperator.domain) :
    ((u : GW.Fock.Carrier),GW.Fock.numberOperator u) ∈
      (fockRealMultiplier (fun n _ => (n : ℝ))).graph := by
  apply (fockRealMultiplier_graph_ae_iff _ _ _).mpr
  intro n
  rw [GW.Fock.numberDiagonal_apply, map_smul]
  exact (Lp.coeFn_smul (n : ℂ) (physicalSector n ((u : GW.Fock.Carrier) n))).symm

theorem numberOperator_preserves_core (u : GW.Fock.numberOperator.domain)
    (hu : (u : GW.Fock.Carrier) ∈ boundedMomentumCore) :
    GW.Fock.numberOperator u ∈ boundedMomentumCore :=
  multiplier_graph_preserves_core (fun n _ => (n : ℝ)) ⟨u,hu⟩ _ (retainedNumber_graph_is_multiplier u)

end Froehlich
