import Froehlich.Nodes.PT01RegularSourceGlobal
import Froehlich.Nodes.PT01CoreCutoffGlobal
import Froehlich.Nodes.UV01Fields

/-! Literal X/Y specializations of the proved regular-source pull-through,
with actual number-domain representatives on both cutoff and singular sides. -/
noncomputable section
open MeasureTheory
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

def auxiliaryXNumber (P : GW.Space) (z : HighSectorSpace 2) : NumberFormSpace :=
  ptRegularSingularNumberVector 2 e (-P) (by norm_num) he g hg hs z

def cutoffAuxiliaryXNumber (Λ : GW.Operators.PositiveCutoff) (P : GW.Space)
    (z : HighSectorSpace 2) : NumberFormSpace :=
  ptRegularCutoffNumberVector 2 e (-P) (by norm_num) he g hg hs z Λ

theorem auxiliaryXNumber_physical (P : GW.Space) (z : HighSectorSpace 2) :
    numberFormEmbedding (auxiliaryXNumber e he g hg hs P z) =
      auxiliaryX e he g hg hs P (z : GW.Fock.Carrier) := by
  rw [auxiliaryXNumber,ptRegularSingularNumberVector_physical]
  exact (auxiliaryExtendedResolvent_on_high 2 e (-P) he g hg hs z).symm

theorem cutoffAuxiliaryXNumber_physical (Λ : GW.Operators.PositiveCutoff)
    (P : GW.Space) (z : HighSectorSpace 2) :
    numberFormEmbedding (cutoffAuxiliaryXNumber e he g hg hs Λ P z) =
      cutoffAuxiliaryX e he Λ g hg hs P (z : GW.Fock.Carrier) := by
  rw [cutoffAuxiliaryXNumber,ptRegularCutoffNumberVector_physical]
  exact (cutoffAuxiliaryExtendedResolvent_on_high 2 e (-P) he Λ g hg hs z).symm

theorem auxiliaryX_pullthrough (P : GW.Space) (z : NumberFormSpace)
    (hz : numberFormEmbedding z ∈ HighSectorSpace 2) :
    ∀ᵐ k ∂volume, annihilationField (auxiliaryXNumber e he g hg hs P ⟨numberFormEmbedding z,hz⟩) k =
      auxiliaryY e (k-P) he g hg hs
        (annihilationField z k - (fiberFormFactor g k : ℂ) •
          auxiliaryX e he g hg hs P (numberFormEmbedding z)) := by
  have hpt := uncutPullthrough_global_source_domain 1 e (-P) (by norm_num) he g hg hs z hz
  filter_upwards [hpt] with k hk
  obtain ⟨q,hq,hout⟩ := hk
  have hx := (auxiliaryExtendedResolvent_on_high 2 e (-P) he g hg hs
    (⟨numberFormEmbedding z,hz⟩ : HighSectorSpace 2)).symm
  change (auxiliaryResolvent 2 e (-P) he g hg hs ⟨numberFormEmbedding z,hz⟩ : GW.Fock.Carrier) =
    auxiliaryX e he g hg hs P (numberFormEmbedding z) at hx
  rw [hx] at hq
  calc
    _ = (auxiliaryResolvent 1 e (-P+k) he g hg hs q : GW.Fock.Carrier) := hout
    _ = auxiliaryY e (-P+k) he g hg hs (q : GW.Fock.Carrier) :=
      (auxiliaryExtendedResolvent_on_high 1 e (-P+k) he g hg hs q).symm
    _ = _ := by rw [hq,show -P+k=k-P by abel]

theorem cutoffAuxiliaryX_pullthrough (Λ : GW.Operators.PositiveCutoff) (P : GW.Space)
    (z : NumberFormSpace) (hz : numberFormEmbedding z ∈ HighSectorSpace 2) :
    ∀ᵐ k ∂volume,
      annihilationField (cutoffAuxiliaryXNumber e he g hg hs Λ P ⟨numberFormEmbedding z,hz⟩) k =
      cutoffAuxiliaryY e (k-P) he Λ g hg hs
        (annihilationField z k - (cutoffFormFactor g Λ.val k : ℂ) •
          cutoffAuxiliaryX e he Λ g hg hs P (numberFormEmbedding z)) := by
  have hpt := cutoffPullthrough_global_source_domain 1 e (-P) (by norm_num) he Λ g hg hs z hz
  filter_upwards [hpt] with k hk
  obtain ⟨q,hq,hout⟩ := hk
  rw [←ptRegularCutoffNumberVector_eq_graph 2 e (-P) (by norm_num) he g hg hs
    (⟨numberFormEmbedding z,hz⟩ : HighSectorSpace 2) Λ] at hout
  have hx := (cutoffAuxiliaryExtendedResolvent_on_high 2 e (-P) he Λ g hg hs
    (⟨numberFormEmbedding z,hz⟩ : HighSectorSpace 2)).symm
  change (cutoffAuxiliaryResolvent 2 e (-P) he Λ g hg hs ⟨numberFormEmbedding z,hz⟩ : GW.Fock.Carrier) =
    cutoffAuxiliaryX e he Λ g hg hs P (numberFormEmbedding z) at hx
  rw [hx] at hq
  calc
    _ = (cutoffAuxiliaryResolvent 1 e (-P+k) he Λ g hg hs q : GW.Fock.Carrier) := hout
    _ = cutoffAuxiliaryY e (-P+k) he Λ g hg hs (q : GW.Fock.Carrier) :=
      (cutoffAuxiliaryExtendedResolvent_on_high 1 e (-P+k) he Λ g hg hs q).symm
    _ = _ := by rw [hq,show -P+k=k-P by abel]

end Froehlich
