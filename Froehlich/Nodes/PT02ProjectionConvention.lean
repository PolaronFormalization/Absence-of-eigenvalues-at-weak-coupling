import Froehlich.Nodes.PT02XField

/-! Number-domain high projections and the paper's X/Y input convention.
Y removes the vacuum output of the discarded one-particle component. -/
noncomputable section
open MeasureTheory
namespace Froehlich

private theorem projectedInverse_absorb (n : ℕ)
    (R : HighSectorSpace n →L[ℂ] HighSectorSpace n) (u : GW.Fock.Carrier) :
    (R (highSectorProject n (highSectorProjection n u)) : GW.Fock.Carrier) =
      (R (highSectorProject n u) : GW.Fock.Carrier) := by
  have hp : highSectorProject n (highSectorProjection n u) = highSectorProject n u := by
    apply Subtype.ext
    exact congrArg (fun A : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier => A u)
      (highSectorProjection_idempotent n)
  rw [hp]

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem auxiliaryY_project (q : GW.Space) (u : GW.Fock.Carrier) :
    auxiliaryY e q he g hg hs (highSectorProjection 1 u) = auxiliaryY e q he g hg hs u :=
  projectedInverse_absorb 1 (auxiliaryResolvent 1 e q he g hg hs) u

theorem auxiliaryX_project (P : GW.Space) (u : GW.Fock.Carrier) :
    auxiliaryX e he g hg hs P (highSectorProjection 2 u) = auxiliaryX e he g hg hs P u :=
  projectedInverse_absorb 2 (auxiliaryResolvent 2 e (-P) he g hg hs) u

theorem cutoffAuxiliaryY_project (Λ : GW.Operators.PositiveCutoff) (q : GW.Space) (u : GW.Fock.Carrier) :
    cutoffAuxiliaryY e q he Λ g hg hs (highSectorProjection 1 u) = cutoffAuxiliaryY e q he Λ g hg hs u :=
  projectedInverse_absorb 1 (cutoffAuxiliaryResolvent 1 e q he Λ g hg hs) u

theorem cutoffAuxiliaryX_project (Λ : GW.Operators.PositiveCutoff) (P : GW.Space) (u : GW.Fock.Carrier) :
    cutoffAuxiliaryX e he Λ g hg hs P (highSectorProjection 2 u) = cutoffAuxiliaryX e he Λ g hg hs P u :=
  projectedInverse_absorb 2 (cutoffAuxiliaryResolvent 2 e (-P) he Λ g hg hs) u

def projectedAuxiliaryXNumber (P : GW.Space) (z : NumberFormSpace) : NumberFormSpace :=
  auxiliaryXNumber e he g hg hs P (highSectorProject 2 (numberFormEmbedding z))

def projectedCutoffAuxiliaryXNumber (Λ : GW.Operators.PositiveCutoff) (P : GW.Space)
    (z : NumberFormSpace) : NumberFormSpace :=
  cutoffAuxiliaryXNumber e he g hg hs Λ P (highSectorProject 2 (numberFormEmbedding z))

theorem projectedAuxiliaryXNumber_physical (P : GW.Space) (z : NumberFormSpace) :
    numberFormEmbedding (projectedAuxiliaryXNumber e he g hg hs P z) =
      auxiliaryX e he g hg hs P (numberFormEmbedding z) := by
  rw [projectedAuxiliaryXNumber,auxiliaryXNumber_physical]
  exact auxiliaryX_project e he g hg hs P (numberFormEmbedding z)

theorem projectedCutoffAuxiliaryXNumber_physical (Λ : GW.Operators.PositiveCutoff)
    (P : GW.Space) (z : NumberFormSpace) :
    numberFormEmbedding (projectedCutoffAuxiliaryXNumber e he g hg hs Λ P z) =
      cutoffAuxiliaryX e he Λ g hg hs P (numberFormEmbedding z) := by
  rw [projectedCutoffAuxiliaryXNumber,cutoffAuxiliaryXNumber_physical]
  exact cutoffAuxiliaryX_project e he g hg hs Λ P (numberFormEmbedding z)

theorem auxiliaryY_annihilation_projection (P : GW.Space) (z : NumberFormSpace) :
    ∀ᵐ k ∂volume, auxiliaryY e (k-P) he g hg hs
      (annihilationField (numberFormHighProjection 2 z) k) =
      auxiliaryY e (k-P) he g hg hs (annihilationField z k) := by
  filter_upwards [annihilationField_highProjection_ae 1 z] with k hk
  rw [hk,auxiliaryY_project]

theorem projectedAuxiliaryX_pullthrough (P : GW.Space) (z : NumberFormSpace) :
    ∀ᵐ k ∂volume, annihilationField (projectedAuxiliaryXNumber e he g hg hs P z) k =
      auxiliaryY e (k-P) he g hg hs (annihilationField z k - (fiberFormFactor g k : ℂ) •
        auxiliaryX e he g hg hs P (numberFormEmbedding z)) := by
  have hz : numberFormEmbedding (numberFormHighProjection 2 z) ∈ HighSectorSpace 2 := by
    rw [numberFormEmbedding_highProjection]
    exact (highSectorProject 2 (numberFormEmbedding z)).property
  have hi : (⟨numberFormEmbedding (numberFormHighProjection 2 z),hz⟩ : HighSectorSpace 2) =
      highSectorProject 2 (numberFormEmbedding z) := Subtype.ext (numberFormEmbedding_highProjection 2 z)
  have hp := auxiliaryX_pullthrough e he g hg hs P (numberFormHighProjection 2 z) hz
  rw [hi] at hp
  filter_upwards [hp,auxiliaryY_annihilation_projection e he g hg hs P z] with k hk ha
  rw [numberFormEmbedding_highProjection,auxiliaryX_project] at hk
  rw [map_sub,ha] at hk
  rw [map_sub]
  exact hk

theorem projectedCutoffAuxiliaryX_pullthrough (Λ : GW.Operators.PositiveCutoff)
    (P : GW.Space) (z : NumberFormSpace) :
    ∀ᵐ k ∂volume, annihilationField (projectedCutoffAuxiliaryXNumber e he g hg hs Λ P z) k =
      cutoffAuxiliaryY e (k-P) he Λ g hg hs (annihilationField z k - (cutoffFormFactor g Λ.val k : ℂ) •
        cutoffAuxiliaryX e he Λ g hg hs P (numberFormEmbedding z)) := by
  have hz : numberFormEmbedding (numberFormHighProjection 2 z) ∈ HighSectorSpace 2 := by
    rw [numberFormEmbedding_highProjection]
    exact (highSectorProject 2 (numberFormEmbedding z)).property
  have hi : (⟨numberFormEmbedding (numberFormHighProjection 2 z),hz⟩ : HighSectorSpace 2) =
      highSectorProject 2 (numberFormEmbedding z) := Subtype.ext (numberFormEmbedding_highProjection 2 z)
  have hp := cutoffAuxiliaryX_pullthrough e he g hg hs Λ P (numberFormHighProjection 2 z) hz
  rw [hi] at hp
  filter_upwards [hp,annihilationField_highProjection_ae 1 z] with k hk ha
  rw [numberFormEmbedding_highProjection,cutoffAuxiliaryX_project] at hk
  rw [map_sub,ha,cutoffAuxiliaryY_project] at hk
  rw [map_sub]
  exact hk

end Froehlich
