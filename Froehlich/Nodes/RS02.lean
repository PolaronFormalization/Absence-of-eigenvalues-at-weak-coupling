import Froehlich.Nodes.RS02ResolventBounds
import Froehlich.Nodes.RS02SourceDerivativesCompositionFinalBounds
import Froehlich.Nodes.RS02WeightedSource
import Froehlich.Nodes.RS01

set_option autoImplicit false

/-! RS02 / lem:derivatives. All constants precede coupling, reference energy
and momentum. Every derivative is of the actual bounded operator or source. -/
noncomputable section
namespace Froehlich
open scoped BoundedEndReal
local instance rs02FinalHighGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance rs02FinalEndGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance rs02FinalEndReal (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace
local instance rs02FinalFockReal : NormedSpace ℝ GW.Fock.Carrier := NormedSpace.restrictScalars ℝ ℂ _

def RS02Quantitative (C : (Fin 3 → ℕ) → ℝ) (Cw e : ℝ)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) : Prop :=
  (∀ (n : ℕ), n ≤ 2 → ContDiff ℝ 3 (fun p : GW.Space => auxiliaryResolvent n e p he g hg hs)) ∧
  ContDiff ℝ 3 (fun p : GW.Space => auxiliaryGroundSourceVector e p he g hg hs) ∧
  (∀ (alpha : Fin 3 → ℕ), (∑ i, alpha i) ≤ 3 → ∀ (n : ℕ), n ≤ 2 → ∀ q : Fin 3 → ℝ,
    coordinateMultiPartial alpha
      (fun t => auxiliaryResolvent n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs) q =
      (auxiliaryPhysicalFreeInverse n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he.2).comp
        ((auxiliaryResolventMiddleJet alpha n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he g hg hs).comp
          (auxiliaryPhysicalFreeInverse n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he.2)) ∧
    ‖auxiliaryResolventMiddleJet alpha n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he g hg hs‖ ≤ C alpha ∧
    ‖coordinateMultiPartial alpha
      (fun t => auxiliaryGroundSourceVector e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs) q‖ ≤ C alpha*|g|) ∧
  (∀ p : GW.Space, auxiliaryGroundSourceVector e p he g hg hs ∈ HighSectorSpace 1 ∧
    (auxiliaryEnergyEmbedding 1 e p he.2 (auxiliaryGroundSourceWeighted g e p he hg hs) : GW.Fock.Carrier) =
      auxiliaryGroundSourceVector e p he g hg hs ∧
    ‖auxiliaryGroundSourceWeighted g e p he hg hs‖ ≤ Cw*|g|)

theorem finalRS02_uniform : ∃ C : (Fin 3 → ℕ) → ℝ, ∃ Cw : ℝ,
    (∀ alpha, 0 < C alpha) ∧ 0 < Cw ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2), RS02Quantitative C Cw e he g hg hs := by
  classical
  have hEach (alpha : Fin 3 → ℕ) : ∃ C : ℝ, 0 < C ∧
      ∀ (_ha : (∑ i, alpha i) ≤ 3) (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
        (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (n : ℕ) (hn : n ≤ 2) (q : Fin 3 → ℝ),
        ‖auxiliaryResolventMiddleJet alpha n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he g hg hs‖ ≤ C ∧
        ‖coordinateMultiPartial alpha
          (fun t => auxiliaryGroundSourceVector e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs) q‖ ≤ C*|g| := by
    by_cases ha : (∑ i, alpha i) ≤ 3
    · obtain ⟨CR,hCR,hR⟩ := auxiliaryResolventMiddleJet_uniform alpha ha
      obtain ⟨CH,hCH,hH⟩ := auxiliaryGroundSourceVector_derivatives_uniform alpha ha
      refine ⟨CR+CH,add_pos hCR hCH,?_⟩
      intro _ g e he hg hs n hn q
      constructor
      · exact (hR n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) hn he g hg hs).trans (le_add_of_nonneg_right hCH.le)
      · have h := hH g e he hg hs q
        exact h.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCR.le) (abs_nonneg g))
    · exact ⟨1,one_pos,fun h => False.elim (ha h)⟩
  choose C hC hBounds using hEach
  obtain ⟨Cw,hCw,hW⟩ := auxiliaryGroundSourceWeighted_uniform_linear
  refine ⟨C,Cw,hC,hCw,?_⟩
  intro e he g hg hs
  refine ⟨?_,?_,?_,?_⟩
  · intro n hn
    simpa only [] using! auxiliaryResolvent_contDiff g n e hn he hg hs
  · simpa only [] using! auxiliaryGroundSourceVector_contDiff g e he hg hs
  · intro alpha ha n hn q
    exact ⟨auxiliaryResolvent_multiPartial_factor alpha ha n e hn he g hg hs q,
      hBounds alpha ha g e he hg hs n hn q⟩
  · intro p
    exact ⟨auxiliaryGroundSourceVector_mem_high g e p he hg hs,
      auxiliaryGroundSourceWeighted_physical g e p he hg hs,hW g e p he hg hs⟩

theorem finalRS02 : ∃ C : (Fin 3 → ℕ) → ℝ, ∃ Cw s : ℝ,
    (∀ alpha, 0 < C alpha) ∧ 0 < Cw ∧ 0 < s ∧ ∀ g : ℝ, |g| < s →
      ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
      ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
        RS02Quantitative C Cw (groundEnergy (fiberHamiltonian g 0)) he g hg hs := by
  obtain ⟨C,Cw,hC,hCw,hAll⟩ := finalRS02_uniform
  obtain ⟨s,hs,hGround⟩ := auxiliarySelfEnergy_zero_groundEnergy
  refine ⟨C,Cw,s,hC,hCw,hs,?_⟩
  intro g hg
  obtain ⟨he,hg1,hsmall,_⟩ := hGround g hg
  exact ⟨he,hg1,hsmall,hAll _ he g hg1 hsmall⟩

end Froehlich
