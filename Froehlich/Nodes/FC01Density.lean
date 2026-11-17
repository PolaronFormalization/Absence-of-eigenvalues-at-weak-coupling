import Froehlich.Nodes.FC01

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology
namespace Froehlich

theorem configurationBall_exhausts (n : ℕ) (k : GW.Fock.Coordinates n) :
    ∀ᶠ R : ℕ in atTop, k ∈ configurationBall n (R : ℝ) := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (∑ i : Fin n, ‖k i‖))] with R hR
  intro i
  exact (Finset.single_le_sum (fun j _ => norm_nonneg (k j)) (Finset.mem_univ i)).trans hR

def unweightedSectorCoordinates (n : ℕ) :=
  GW.Spaces.WeightedL2.coordinates (H := ℂ)
    (w := fun _ : GW.Fock.Coordinates n => (1 : ℝ)) (μ := GW.Fock.sectorMeasure n)

theorem physicalSector_momentumCutoff (R : ℝ) (n : ℕ) (u : GW.Fock.Sector n) :
    physicalSector n (sectorMomentumCutoff R n u) =
      unweightedSectorCoordinates n
        (GW.Spaces.WeightedL2.cutoff (w := fun _ : GW.Fock.Coordinates n => (1 : ℝ))
          (configurationBall n R) (configurationBall_measurable n R)
          ((unweightedSectorCoordinates n).symm (physicalSector n u))) := by
  apply Lp.ext
  filter_upwards [sectorMomentumCutoff_ae R n u,
    GW.Spaces.WeightedL2.cutoff_ae (w := fun _ : GW.Fock.Coordinates n => (1 : ℝ))
      (configurationBall n R) (configurationBall_measurable n R)
      ((unweightedSectorCoordinates n).symm (physicalSector n u))] with k hk hc
  change (configurationBall n R).indicator (physicalSector n u : _ → ℂ) k = _ at hc
  rw [← hk]
  calc
    _ = (configurationBall n R).indicator (physicalSector n u : _ → ℂ) k := by
      by_cases hm : k ∈ configurationBall n R <;> simp [configurationIndicator, hm]
    _ = _ := hc

theorem sectorMomentumCutoff_tendsto (n : ℕ) (u : GW.Fock.Sector n) :
    Tendsto (fun R : ℕ => sectorMomentumCutoff (R : ℝ) n u) atTop (𝓝 u) := by
  apply (physicalSector n).isometry.tendsto_nhds_iff.mpr
  have ht := GW.Spaces.WeightedL2.cutoff_tendsto
    (w := fun _ : GW.Fock.Coordinates n => (1 : ℝ))
    (fun R : ℕ => configurationBall n (R : ℝ))
    (fun R => configurationBall_measurable n (R : ℝ))
    (Eventually.of_forall (configurationBall_exhausts n))
    ((unweightedSectorCoordinates n).symm (physicalSector n u))
  have hc := (unweightedSectorCoordinates n).continuous.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, ← physicalSector_momentumCutoff,
    LinearIsometryEquiv.apply_symm_apply] using hc

def boundedMomentumFiber (R n : ℕ) : GW.Fock.Sector n →L[ℂ] GW.Fock.Sector n :=
  if n ≤ R then sectorMomentumCutoff (R : ℝ) n else 0

theorem boundedMomentumFiber_norm (R n : ℕ) : ‖boundedMomentumFiber R n‖ ≤ 1 := by
  unfold boundedMomentumFiber
  split_ifs
  · exact sectorMomentumCutoff_norm _ _
  · simp

theorem boundedMomentumFiber_tendsto (n : ℕ) (u : GW.Fock.Sector n) :
    Tendsto (fun R => boundedMomentumFiber R n u) atTop (𝓝 u) := by
  apply (sectorMomentumCutoff_tendsto n u).congr'
  filter_upwards [eventually_ge_atTop n] with R hR
  simp only [boundedMomentumFiber, if_pos hR]

theorem boundedMomentumProjection_tendsto (u : GW.Fock.Carrier) :
    Tendsto (fun R => boundedMomentumProjection R R u) atTop (𝓝 u) := by
  have ht := GW.Spaces.diagonalMap_tendsto boundedMomentumFiber boundedMomentumFiber_norm
    boundedMomentumFiber_tendsto u
  have he (R : ℕ) : GW.Spaces.diagonalMap (boundedMomentumFiber R) zero_le_one
      (boundedMomentumFiber_norm R) u = boundedMomentumProjection R R u := by
    apply lp.ext
    funext n
    change boundedMomentumFiber R n (u n) = _
    rw [boundedMomentumProjection_apply]
    unfold boundedMomentumFiber
    split_ifs <;> rfl
  simpa only [he] using ht

theorem boundedMomentumCore_dense : Dense (boundedMomentumCore : Set GW.Fock.Carrier) := by
  intro u
  apply mem_closure_of_tendsto (boundedMomentumProjection_tendsto u)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with R hR
  exact ⟨R,R,hR,hR,boundedMomentumProjection_idempotent R R u⟩

theorem numberFormEmbedding_boundedMomentumProjection (M R : ℕ) (x : NumberFormSpace) :
    numberFormEmbedding (show NumberFormSpace from boundedMomentumProjection M R x) =
      boundedMomentumProjection M R (numberFormEmbedding x) := by
  apply lp.ext
  funext n
  rw [numberFormEmbedding_apply]
  change (↑(((n : ℝ)+1)^(-(1/2 : ℝ))) : ℂ) •
    (boundedMomentumProjection M R (show GW.Fock.Carrier from x)) n =
      boundedMomentumProjection M R (numberFormEmbedding x) n
  rw [boundedMomentumProjection_apply, boundedMomentumProjection_apply, numberFormEmbedding_apply]
  by_cases hn : n ≤ M
  · simp only [if_pos hn, map_smul]
  · simp only [if_neg hn, smul_zero]

theorem coreNumberLift_denseRange : DenseRange coreNumberLift := by
  intro x
  let v : ℕ → NumberFormSpace := fun R => boundedMomentumProjection R R x
  have ht : Tendsto v atTop (𝓝 x) := boundedMomentumProjection_tendsto x
  apply mem_closure_of_tendsto ht
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with R hR
  have hu : numberFormEmbedding (v R) ∈ boundedMomentumCore := by
    rw [numberFormEmbedding_boundedMomentumProjection]
    exact ⟨R,R,hR,hR,boundedMomentumProjection_idempotent R R (numberFormEmbedding x)⟩
  refine ⟨⟨numberFormEmbedding (v R),hu⟩,?_⟩
  apply numberFormEmbedding_injective
  exact coreNumberLift_embedding _

end Froehlich
