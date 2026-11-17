import Froehlich.Nodes.FC04Continuous
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The actual fixed-energy continuous linear field map and native L²(K)
restriction. Linearity is identified through the physical embedding. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace Classical
namespace Froehlich

def energyZeroFieldEmbedding :
    Lp (EnergySpace 0) 2 (volume : Measure GW.Space) →L[ℂ]
      Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) :=
  (energyEmbedding 0).compLpL 2 volume

theorem energyZeroFieldEmbedding_injective : Function.Injective energyZeroFieldEmbedding := by
  intro u v huv
  apply Lp.ext
  filter_upwards [(energyEmbedding 0).coeFn_compLp u, (energyEmbedding 0).coeFn_compLp v]
    with k hu hv
  apply energyEmbedding_injective 0
  have he := congrArg (fun z : Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) => z k) huv
  exact hu.symm.trans (he.trans hv)

def fixedPhysicalFieldMap (P : GW.Space) (K : Set GW.Space) (hK : MeasurableSet K) :
    OperatorGraphSpace P →L[ℂ] Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) :=
  (GW.Analysis.boundedMultiplier (K.indicator (fun _ : GW.Space => (1 : ℂ)))
    (measurable_const.indicator hK) (C := (1 : ℝ))
    (Eventually.of_forall (fun k => by
      by_cases hk : k ∈ K <;> simp [hk]))).comp
      (annihilationField.comp (freeGraphNumberCoordinates P))

section FixedSet
variable (P : GW.Space) (K : Set GW.Space) (hK : MeasurableSet K)
  (R : ℝ) (hR : 0 ≤ R) (hKR : ∀ k ∈ K, ‖k‖ ≤ R)

theorem fixedEnergyField_physical_map (x : OperatorGraphSpace P) :
    energyZeroFieldEmbedding (fixedEnergyField P K hK R hR hKR x) = fixedPhysicalFieldMap P K hK x := by
  apply Lp.ext
  have hm := GW.Analysis.boundedMultiplier_ae (K.indicator (fun _ : GW.Space => (1 : ℂ)))
    (measurable_const.indicator hK) (C := (1 : ℝ))
    (Eventually.of_forall (fun k => by by_cases hk : k ∈ K <;> simp [hk]))
    (annihilationField (freeGraphNumberCoordinates P x))
  filter_upwards [(energyEmbedding 0).coeFn_compLp (fixedEnergyField P K hK R hR hKR x),
    fixedEnergyField_embedding P K hK R hR hKR x, hm] with k hj hp hm
  have hleft : energyZeroFieldEmbedding (fixedEnergyField P K hK R hR hKR x) k =
      energyEmbedding 0 (fixedEnergyField P K hK R hR hKR x k) := hj
  have hright : (K.indicator (fun _ : GW.Space => (1 : ℂ)) k) •
      annihilationField (freeGraphNumberCoordinates P x) k = fixedPhysicalFieldMap P K hK x k := hm
  rw [hleft, hp, ← hright]
  by_cases hk : k ∈ K <;> simp [hk]

def fixedEnergyFieldLinear :
    OperatorGraphSpace P →ₗ[ℂ] Lp (EnergySpace 0) 2 (volume : Measure GW.Space) where
  toFun := fixedEnergyField P K hK R hR hKR
  map_add' x y := by
    apply energyZeroFieldEmbedding_injective
    rw [map_add, fixedEnergyField_physical_map, fixedEnergyField_physical_map,
      fixedEnergyField_physical_map, map_add]
  map_smul' c x := by
    apply energyZeroFieldEmbedding_injective
    rw [map_smul, fixedEnergyField_physical_map, fixedEnergyField_physical_map, map_smul]
    simp only [RingHom.id_apply]

def fixedEnergyFieldMap :
    OperatorGraphSpace P →L[ℂ] Lp (EnergySpace 0) 2 (volume : Measure GW.Space) :=
  (fixedEnergyFieldLinear P K hK R hR hKR).mkContinuous (fixedEnergyFieldConstant P R)
    (fixedEnergyField_bound P K hK R hR hKR)

theorem fixedEnergyFieldMap_opNorm :
    ‖fixedEnergyFieldMap P K hK R hR hKR‖ ≤ fixedEnergyFieldConstant P R := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  exact fixedEnergyField_bound P K hK R hR hKR

def restrictedEnergyFieldMap :
    OperatorGraphSpace P →L[ℂ] Lp (EnergySpace 0) 2 ((volume : Measure GW.Space).restrict K) :=
  (LpToLpRestrictCLM GW.Space (EnergySpace 0) ℂ volume 2 K).comp
    (fixedEnergyFieldMap P K hK R hR hKR)

theorem restrictedEnergyFieldMap_physical (x : OperatorGraphSpace P) :
    ∀ᵐ k ∂((volume : Measure GW.Space).restrict K),
      energyEmbedding 0 (restrictedEnergyFieldMap P K hK R hR hKR x k) =
        annihilationField (freeGraphNumberCoordinates P x) k := by
  have hj := ae_restrict_of_ae (s := K) (fixedEnergyField_embedding P K hK R hR hKR x)
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ K (fixedEnergyField P K hK R hR hKR x),
    hj, ae_restrict_mem hK] with k hk hj hmem
  have he : restrictedEnergyFieldMap P K hK R hR hKR x k =
      fixedEnergyField P K hK R hR hKR x k := hk
  rw [he, hj, Set.indicator_of_mem hmem]

end FixedSet
end Froehlich
