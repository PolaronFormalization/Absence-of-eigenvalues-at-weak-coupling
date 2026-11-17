import Froehlich.Nodes.FC01

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

theorem vacuum_mem_boundedMomentumCore : GW.Fock.vacuum ∈ boundedMomentumCore := by
  refine ⟨1,1,le_rfl,le_rfl,?_⟩
  apply lp.ext
  funext n
  rw [boundedMomentumProjection_apply]
  cases n with
  | zero => rfl
  | succ n => simp [GW.Fock.vacuum_succ]

theorem sectorProjection_preserves_core (m : ℕ) (u : boundedMomentumCore) :
    sectorProjection m u ∈ boundedMomentumCore := by
  obtain ⟨M,R,hM,hR,hfinite,hsupport⟩ := boundedMomentumCore_support u
  apply boundedMomentumCore_mem_of_support M R hM hR
  · intro n hn
    rw [sectorProjection_apply]
    by_cases hnm : n = m
    · subst n
      rw [lp.single_apply_self, hfinite m hn]
    · exact lp.single_apply_ne _ _ _ hnm
  · intro n
    rw [sectorProjection_apply]
    by_cases hnm : n = m
    · subst n
      rw [lp.single_apply_self]
      exact hsupport m
    · rw [lp.single_apply_ne _ _ _ hnm, map_zero]
      filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := GW.Fock.sectorMeasure n)] with k hk
      intro _
      simpa only [Pi.zero_apply] using hk

theorem lowSectorProjection_preserves_core (m : ℕ) (u : boundedMomentumCore) :
    lowSectorProjection m u ∈ boundedMomentumCore := by
  change GW.Fock.cutoff GW.Fock.Sector m (u : GW.Fock.Carrier) ∈ boundedMomentumCore
  rw [GW.Fock.cutoff_sum]
  apply Submodule.sum_mem
  intro n hn
  exact sectorProjection_preserves_core n u

theorem highSectorProjection_preserves_core (m : ℕ) (u : boundedMomentumCore) :
    highSectorProjection m u ∈ boundedMomentumCore := by
  cases m with
  | zero => exact u.property
  | succ m =>
    change (u : GW.Fock.Carrier) - lowSectorProjection m u ∈ boundedMomentumCore
    exact boundedMomentumCore.sub_mem u.property (lowSectorProjection_preserves_core m u)

end Froehlich
