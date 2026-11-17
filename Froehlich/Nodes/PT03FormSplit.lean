import Froehlich.Nodes.PT03ScalarStepThree
import Froehlich.Nodes.PT03FormKernelIntegrability
import Froehlich.Nodes.PT03BoundsDiagonalContinuity

set_option autoImplicit false

/-! Absolute scalar splitting of the actual finite-cutoff correction on
the one-particle form domain, with the product integral justified by Fubini. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem cutoffCorrection_split_integrals (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4) (Λ : GW.Operators.PositiveCutoff)
    (f h : OneParticleEnergySpace P) :
    let F := oneParticleEnergyEmbedding P f
    let H := oneParticleEnergyEmbedding P h
    Integrable (fun k => (starRingEnd ℂ) (F k)*cutoffThresholdDiagonal e he g hg hs Λ (k-P)*H k) volume ∧
    Integrable (fun x : GW.Space × GW.Space => (starRingEnd ℂ) (F x.1) * (cutoffFormFactor g Λ.val x.1 : ℂ) *
      cutoffThresholdKernelJ e he g hg hs Λ P (x.1-P) (x.2-P) * (cutoffFormFactor g Λ.val x.2 : ℂ) * H x.2)
      (volume.prod volume) ∧
    ⟪(oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) F : GW.Fock.Carrier),
      cutoffAuxiliaryX e he Λ g hg hs P
        (oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) H : GW.Fock.Carrier)⟫_ℂ =
      (∫ k, (starRingEnd ℂ) (F k)*cutoffThresholdDiagonal e he g hg hs Λ (k-P)*H k) +
      ∫ x : GW.Space × GW.Space, (starRingEnd ℂ) (F x.1) * (cutoffFormFactor g Λ.val x.1 : ℂ) *
        cutoffThresholdKernelJ e he g hg hs Λ P (x.1-P) (x.2-P) * (cutoffFormFactor g Λ.val x.2 : ℂ) * H x.2 := by
  intro F H
  let S := fun x : GW.Space × GW.Space => (starRingEnd ℂ) (F x.1) * (cutoffFormFactor g Λ.val x.1 : ℂ) *
    cutoffThresholdKernelJ e he g hg hs Λ P (x.1-P) (x.2-P) * (cutoffFormFactor g Λ.val x.2 : ℂ) * H x.2
  have hS : Integrable S (volume.prod volume) := cutoffThresholdKernelJ_form_integrable e he g hg hs P hP Λ f h
  have hD := cutoffThresholdDiagonal_shift_integrable e he g hg hs Λ P F H
  refine ⟨hD,hS,?_⟩
  have hiter (k : GW.Space) : (starRingEnd ℂ) (F k) * (cutoffFormFactor g Λ.val k : ℂ) *
      (∫ l, H l * (cutoffFormFactor g Λ.val l : ℂ) * cutoffThresholdKernelJ e he g hg hs Λ P (k-P) (l-P)) =
        ∫ l, S (k,l) := by
    calc
      _ = ∫ l, ((starRingEnd ℂ) (F k) * (cutoffFormFactor g Λ.val k : ℂ)) *
          (H l * (cutoffFormFactor g Λ.val l : ℂ) * cutoffThresholdKernelJ e he g hg hs Λ P (k-P) (l-P)) :=
        (integral_const_mul _ _).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun l => by dsimp only [S]; ring))
  have hrow := (cutoffCorrection_integrated_row e he g hg hs Λ P F H).2
  calc
    _ = ∫ k, (starRingEnd ℂ) (F k) * H k *
        ⟪oneParticleInclusion (cutoffFormFactorL2 g Λ.val Λ.property),
          cutoffAuxiliaryY e (k-P) he Λ g hg hs
            (oneParticleInclusion (cutoffFormFactorL2 g Λ.val Λ.property))⟫_ℂ +
      (starRingEnd ℂ) (F k) * (cutoffFormFactor g Λ.val k : ℂ) *
        (∫ l, H l * (cutoffFormFactor g Λ.val l : ℂ) * cutoffThresholdKernelJ e he g hg hs Λ P (k-P) (l-P)) := hrow
    _ = ∫ k, (starRingEnd ℂ) (F k)*cutoffThresholdDiagonal e he g hg hs Λ (k-P)*H k + ∫ l, S (k,l) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun k => by
        dsimp only
        rw [←cutoffThresholdDiagonal_hilbert e he g hg hs Λ (k-P),hiter]
        ring
    _ = _ := by
      rw [integral_add hD hS.integral_prod_left,←integral_prod S hS]
      rfl

end Froehlich
