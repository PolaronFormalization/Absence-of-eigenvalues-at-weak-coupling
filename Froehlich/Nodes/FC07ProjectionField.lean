import Froehlich.Nodes.FC07MovingCutoff
import Froehlich.Nodes.GW06CompressionCore
import Froehlich.Nodes.GW06ZeroSector

/-! Particle projection and actual shifted compressed core actions. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

def coreHighProjection (n : ℕ) (u : boundedMomentumCore) : boundedMomentumCore :=
  ⟨highSectorProjection n u,highSectorProjection_preserves_core n u⟩

theorem coreHighProjection_numberLift (n : ℕ) (u : boundedMomentumCore) :
    coreNumberLift (coreHighProjection n u) = numberFormHighProjection n (coreNumberLift u) := by
  apply numberFormEmbedding_injective
  rw [coreNumberLift_embedding,numberFormEmbedding_highProjection,coreNumberLift_embedding]
  rfl

theorem annihilationField_core_highProjection (m : ℕ) (u : boundedMomentumCore) :
    annihilationField (coreNumberLift (coreHighProjection (m+1) u)) =
      (highSectorProjection m).compLp (annihilationField (coreNumberLift u)) := by
  rw [coreHighProjection_numberLift]
  exact annihilationField_highProjection m (coreNumberLift u)

theorem annihilationField_core_highProjection_ae (m : ℕ) (u : boundedMomentumCore) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      annihilationField (coreNumberLift (coreHighProjection (m+1) u)) k =
        highSectorProjection m (annihilationField (coreNumberLift u) k) := by
  rw [coreHighProjection_numberLift]
  exact annihilationField_highProjection_ae m (coreNumberLift u)

theorem coreHighProjection_eq (n : ℕ) (u : boundedMomentumCore)
    (hu : (u : GW.Fock.Carrier) ∈ HighSectorSpace n) : coreHighProjection n u = u := by
  apply Subtype.ext
  exact (highSector_mem_iff n u).mp hu

theorem annihilationField_high_core_ae (m : ℕ) (u : boundedMomentumCore)
    (hu : (u : GW.Fock.Carrier) ∈ HighSectorSpace (m+1)) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      annihilationField (coreNumberLift u) k ∈ HighSectorSpace m := by
  have h := annihilationField_core_highProjection_ae m u
  rw [coreHighProjection_eq (m+1) u hu] at h
  filter_upwards [h] with k hk
  exact (highSector_mem_iff m _).mpr hk.symm

def coreProjectedCutoffShiftAction (g : ℝ) (P : GW.Space) (n : ℕ)
    (Λ : GW.Operators.PositiveCutoff) (e : ℝ) (u : boundedMomentumCore) : boundedMomentumCore :=
  coreHighProjection n (coreCutoffActionCore g P Λ u) - ((e-1+(n : ℝ) : ℝ) : ℂ) • u

def compressedCutoffShiftCoreOutput (g : ℝ) (P : GW.Space) (n : ℕ)
    (Λ : GW.Operators.PositiveCutoff) (e : ℝ) (u : boundedMomentumCore)
    (hu : (u : GW.Fock.Carrier) ∈ HighSectorSpace n) : HighSectorSpace n :=
  highSectorProject n (coreCutoffAction g P Λ u) - ((e-1+(n : ℝ) : ℝ) : ℂ) • ⟨(u : GW.Fock.Carrier),hu⟩

theorem compressedCutoffShiftCoreOutput_coe (g : ℝ) (P : GW.Space) (n : ℕ)
    (Λ : GW.Operators.PositiveCutoff) (e : ℝ) (u : boundedMomentumCore)
    (hu : (u : GW.Fock.Carrier) ∈ HighSectorSpace n) :
    (compressedCutoffShiftCoreOutput g P n Λ e u hu : GW.Fock.Carrier) =
      (coreProjectedCutoffShiftAction g P n Λ e u : GW.Fock.Carrier) := rfl

theorem compressedCutoffShift_core_graph (g : ℝ) (P : GW.Space) (n : ℕ)
    (Λ : GW.Operators.PositiveCutoff) (e : ℝ) (u : boundedMomentumCore)
    (hu : (u : GW.Fock.Carrier) ∈ HighSectorSpace n) :
    ((⟨(u : GW.Fock.Carrier),hu⟩ : HighSectorSpace n),compressedCutoffShiftCoreOutput g P n Λ e u hu) ∈
      (GW.Operators.complexShift (compressedHamiltonian g P n (some Λ)) ((e-1+(n : ℝ) : ℝ) : ℂ)).graph := by
  apply (GW.Operators.complexShift_graph_iff _ _ _).mpr
  change ((⟨(u : GW.Fock.Carrier),hu⟩ : HighSectorSpace n),
    (highSectorProject n (coreCutoffAction g P Λ u) - ((e-1+(n : ℝ) : ℝ) : ℂ) • ⟨(u : GW.Fock.Carrier),hu⟩) +
      ((e-1+(n : ℝ) : ℝ) : ℂ) • ⟨(u : GW.Fock.Carrier),hu⟩) ∈ (compressedHamiltonian g P n (some Λ)).graph
  rw [sub_add_cancel]
  exact compressedCutoff_core_graph g P n Λ u hu

theorem coreProjectedCutoffShiftAction_high (g : ℝ) (P : GW.Space) (n : ℕ)
    (Λ : GW.Operators.PositiveCutoff) (e : ℝ) (u : boundedMomentumCore)
    (hu : (u : GW.Fock.Carrier) ∈ HighSectorSpace n) :
    (coreProjectedCutoffShiftAction g P n Λ e u : GW.Fock.Carrier) ∈ HighSectorSpace n := by
  rw [← compressedCutoffShiftCoreOutput_coe g P n Λ e u hu]
  exact (compressedCutoffShiftCoreOutput g P n Λ e u hu).property

theorem compressed_zero_shift_graph_iff (g : ℝ) (P : GW.Space)
    (i : Option GW.Operators.PositiveCutoff) (c : ℂ) (u f : HighSectorSpace 0) :
    (u,f) ∈ (GW.Operators.complexShift (compressedHamiltonian g P 0 i) c).graph ↔
      ((u : GW.Fock.Carrier),(f : GW.Fock.Carrier)) ∈
        (GW.Operators.complexShift (GW.Operators.formOperator (fiberFormData g P i)) c).graph := by
  rw [GW.Operators.complexShift_graph_iff,GW.Operators.complexShift_graph_iff]
  exact compressed_zero_graph_iff g P i u (f+c • u)

end Froehlich
