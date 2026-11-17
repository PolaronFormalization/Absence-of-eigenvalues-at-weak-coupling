import Froehlich.Nodes.RS02SourceSmoothC3
import Froehlich.Nodes.CA02CanonicalExpansion

set_option autoImplicit false

/-! Canonical derivatives and coupling-uniform bounds for the ACTUAL
normalized singular source, transported from its literal one-particle L2 jets. -/
noncomputable section
namespace Froehlich

local instance rs02SourceDerivativesHighNormedGroup : NormedAddCommGroup (HighSectorSpace 1) :=
  Submodule.normedAddCommGroup (HighSectorSpace 1)
local instance rs02SourceDerivativesHighRealSpace : NormedSpace ℝ (HighSectorSpace 1) :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance rs02SourceDerivativesHighBoundedSMul : IsBoundedSMul ℝ (HighSectorSpace 1) :=
  NormedSpace.toIsBoundedSMul
local instance rs02SourceDerivativesHighContinuousSMul : ContinuousSMul ℝ (HighSectorSpace 1) :=
  IsBoundedSMul.continuousSMul

def auxiliarySourceJetChartHigh (is : List (Fin 3)) (g e : ℝ) (q : Fin 3 → ℝ) (he : e ≤ 0) :
    HighSectorSpace 1 := auxiliarySourceJetHigh is g e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he

theorem auxiliarySourceJetChartHigh_hasDerivAt_update (is : List (Fin 3))
    (g e : ℝ) (he : e ≤ 0) (q : Fin 3 → ℝ) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => auxiliarySourceJetChartHigh is g e (Function.update q i t) he)
      (auxiliarySourceJetChartHigh (i::is) g e q he) (q i) := by
  let L := oneParticleHighInclusion.restrictScalars ℝ
  have hidentity (js : List (Fin 3)) (p : Fin 3 → ℝ) :
      L (auxiliarySourceJetChartL2 js g e p he) = auxiliarySourceJetChartHigh js g e p he :=
    auxiliarySourceJetHigh_inclusion js g e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he
  have hd := L.hasFDerivAt.comp_hasDerivAt (q i)
    (auxiliarySourceJetChartL2_hasDerivAt_update is g e he q i)
  have hdc := hd.congr_deriv (hidentity (i::is) q)
  apply hdc.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t => (hidentity is (Function.update q i t)).symm)

private theorem sourceCoordinateUnitBlocks {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (J : List (Fin 3) → (Fin 3 → ℝ) → V)
    (h : ∀ is p i, HasDerivAt (fun t : ℝ => J is (Function.update p i t)) (J (i::is) p) (p i))
    (is : List (Fin 3)) : coordinateBlocksPartial (is.map (fun i => (i,1))) (J []) = J is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons,coordinateBlocksPartial]
    rw [ih]
    change coordinatePartial i (J is) = J (i::is)
    funext p
    exact (h is p i).deriv

theorem auxiliarySourceJetL2_multiPartial (alpha : Fin 3 → ℕ) (g e : ℝ) (he : e ≤ 0)
    (q : Fin 3 → ℝ) :
    coordinateMultiPartial alpha (fun p => auxiliarySourceJetChartL2 [] g e p he) q =
      auxiliarySourceJetChartL2 (canonicalMultiIndexCoordinates alpha) g e q he := by
  rw [coordinateMultiPartial_eq_unitBlocks]
  have h := sourceCoordinateUnitBlocks (fun is p => auxiliarySourceJetChartL2 is g e p he)
    (fun is p i => auxiliarySourceJetChartL2_hasDerivAt_update is g e he p i)
    (canonicalMultiIndexCoordinates alpha)
  exact congrFun h q

theorem auxiliaryNormalizedSource_multiPartial (alpha : Fin 3 → ℕ) (g e : ℝ)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (q : Fin 3 → ℝ) :
    coordinateMultiPartial alpha
      (fun p => auxiliaryNormalizedSource g e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2) q =
      auxiliarySourceJetChartHigh (canonicalMultiIndexCoordinates alpha) g e q he.2 := by
  have heq : (fun p : Fin 3 → ℝ => auxiliaryNormalizedSource g e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2) =
      (fun p => auxiliarySourceJetChartHigh [] g e p he.2) := by
    funext p
    exact auxiliaryNormalizedSource_eq_sourceJetHigh g e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he
  rw [heq,coordinateMultiPartial_eq_unitBlocks]
  have h := sourceCoordinateUnitBlocks (fun is p => auxiliarySourceJetChartHigh is g e p he.2)
    (fun is p i => auxiliarySourceJetChartHigh_hasDerivAt_update is g e he.2 p i)
    (canonicalMultiIndexCoordinates alpha)
  exact congrFun h q

theorem auxiliaryNormalizedSource_derivatives_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (alpha : Fin 3 → ℕ), (∑ i, alpha i) ≤ 3 → ∀ (g e : ℝ)
      (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (q : Fin 3 → ℝ),
      ‖coordinateMultiPartial alpha
        (fun p => auxiliaryNormalizedSource g e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he.2) q‖ ≤
        scalarDerivativeCoefficientBound (∑ i, alpha i)*C*|g| := by
  obtain ⟨C,hC,hbound⟩ := auxiliarySourceJets_uniform_bound
  refine ⟨C,hC,?_⟩
  intro alpha _ g e he q
  rw [auxiliaryNormalizedSource_multiPartial alpha g e he q]
  have h := hbound (canonicalMultiIndexCoordinates alpha) g e
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he.2
  simpa only [auxiliarySourceJetChartHigh,auxiliarySourceJetHigh_norm,
    canonicalMultiIndexCoordinates_length] using! h

end Froehlich
