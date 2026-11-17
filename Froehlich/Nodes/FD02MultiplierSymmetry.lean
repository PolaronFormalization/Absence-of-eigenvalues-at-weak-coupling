import Froehlich.Nodes.FD02Multipliers

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem sectorRealMultiplier_graph_pairing (n : ℕ) (m : GW.Fock.Coordinates n → ℝ)
    (u f v g : GW.Fock.AmbientSector n)
    (hu : (u,f) ∈ (GW.Analysis.realMultiplier (H := ℂ) m (GW.Fock.sectorMeasure n)).graph)
    (hv : (v,g) ∈ (GW.Analysis.realMultiplier (H := ℂ) m (GW.Fock.sectorMeasure n)).graph) :
    ⟪f,v⟫_ℂ = ⟪u,g⟫_ℂ := by
  obtain ⟨a,rfl,rfl⟩ := (GW.Analysis.realMultiplier (H := ℂ) m (GW.Fock.sectorMeasure n)).mem_graph_iff.mp hu
  obtain ⟨b,rfl,rfl⟩ := (GW.Analysis.realMultiplier (H := ℂ) m (GW.Fock.sectorMeasure n)).mem_graph_iff.mp hv
  exact GW.Analysis.realMultiplier_symmetric m a b

/-- Formal symmetry needs real symbols and actual symmetric output graphs,
not a density or permutation-invariance hypothesis. -/
theorem fockRealMultiplier_symmetric (m : ∀ n, GW.Fock.Coordinates n → ℝ) :
    (fockRealMultiplier m).IsFormalAdjoint (fockRealMultiplier m) := by
  intro u v
  have hu := (fockRealMultiplier_graph_ae_iff m _ _).mp ((fockRealMultiplier m).mem_graph u)
  have hv := (fockRealMultiplier_graph_ae_iff m _ _).mp ((fockRealMultiplier m).mem_graph v)
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  have hgu := (realMultiplier_graph_ae_iff (m n) _ _).mpr (hu n)
  have hgv := (realMultiplier_graph_ae_iff (m n) _ _).mpr (hv n)
  have h := sectorRealMultiplier_graph_pairing n (m n) _ _ _ _ hgu hgv
  simpa only [LinearIsometry.inner_map_map] using h

end Froehlich
