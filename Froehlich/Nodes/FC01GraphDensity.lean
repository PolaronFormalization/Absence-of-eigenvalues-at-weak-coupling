import Froehlich.Nodes.FC01Density

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology
namespace Froehlich

theorem boundedMomentumProjection_ae (M R n : ℕ) (u : GW.Fock.Carrier) :
    physicalSector n (boundedMomentumProjection M R u n) =ᵐ[GW.Fock.sectorMeasure n]
      (fun k => (if n ≤ M then configurationIndicator n (R : ℝ) k else 0) *
        physicalSector n (u n) k) := by
  rw [boundedMomentumProjection_apply]
  by_cases hn : n ≤ M
  · rw [if_pos hn]
    filter_upwards [sectorMomentumCutoff_ae (R : ℝ) n (u n)] with k hk
    simpa only [if_pos hn, smul_eq_mul] using hk.symm
  · rw [if_neg hn, map_zero]
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := GW.Fock.sectorMeasure n)] with k hk
    simp only [Pi.zero_apply] at hk
    simp only [if_neg hn, zero_mul, hk]

/-- A bounded coordinate cutoff commutes with every actual weighted embedding
whose multiplication identity is supplied. No unbounded multiplier is applied
to a vector outside its domain. -/
theorem weightedEmbedding_boundedMomentumProjection
    (j : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier)
    (w : ∀ n, GW.Fock.Coordinates n → ℝ) (hw : ∀ n k, 0 < w n k)
    (hj : ∀ x n, (fun k => (w n k : ℂ) * physicalSector n (j x n) k)
      =ᵐ[GW.Fock.sectorMeasure n] physicalSector n (x n))
    (M R : ℕ) (x : GW.Fock.Carrier) :
    j (boundedMomentumProjection M R x) = boundedMomentumProjection M R (j x) := by
  apply lp.ext
  funext n
  apply (physicalSector n).injective
  apply Lp.ext
  filter_upwards [hj (boundedMomentumProjection M R x) n, hj x n,
    boundedMomentumProjection_ae M R n x,
    boundedMomentumProjection_ae M R n (j x)] with k h1 h2 h3 h4
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (hw n k)))
  rw [h1, h3, h4, ← h2]
  ring

theorem weightedEmbedding_core_dense
    (j : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier)
    (w : ∀ n, GW.Fock.Coordinates n → ℝ) (hw : ∀ n k, 0 < w n k)
    (hj : ∀ x n, (fun k => (w n k : ℂ) * physicalSector n (j x n) k)
      =ᵐ[GW.Fock.sectorMeasure n] physicalSector n (x n)) :
    Dense {x : GW.Fock.Carrier | j x ∈ boundedMomentumCore} := by
  intro x
  apply mem_closure_of_tendsto (boundedMomentumProjection_tendsto x)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with R hR
  change j (boundedMomentumProjection R R x) ∈ boundedMomentumCore
  rw [weightedEmbedding_boundedMomentumProjection j w hw hj]
  exact ⟨R,R,hR,hR,boundedMomentumProjection_idempotent R R (j x)⟩

end Froehlich
