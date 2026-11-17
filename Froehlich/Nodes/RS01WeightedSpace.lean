import Froehlich.Nodes.RS01Weights
import Froehlich.Nodes.FD02WeightedConjugation
import Froehlich.Nodes.GW06Sectors

/-! The actual auxiliary weighted domain restricted to high sectors.
The retained weighted-coordinate isometry gives its canonical Hilbert norm;
no ambient subtype norm is substituted for the weight norm. -/
noncomputable section
namespace Froehlich

def auxiliaryWeightedGraph (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    GW.Spaces.WeightedGraph GW.Fock.Carrier GW.Fock.Carrier :=
  fockWeightedGraph (auxiliaryWeight n e p) (auxiliaryWeight_measurable n e p)
    (fun m K => auxiliaryWeight_ge_one n m e p he K)
    (fun m tau K => auxiliaryWeight_permutation n m e p tau K)

abbrev AuxiliaryFullEnergy (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :=
  GW.Spaces.WeightedDomain (auxiliaryWeightedGraph n e p he)

def auxiliaryWeightedCoordinates (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    AuxiliaryFullEnergy n e p he ≃ₗᵢ[ℂ] GW.Fock.Carrier :=
  fockWeightedCoordinates (auxiliaryWeight n e p) (auxiliaryWeight_measurable n e p)
    (fun m K => auxiliaryWeight_ge_one n m e p he K)
    (fun m tau K => auxiliaryWeight_permutation n m e p tau K)

def auxiliaryFullEmbedding (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    AuxiliaryFullEnergy n e p he →L[ℂ] GW.Fock.Carrier :=
  fockWeightedInclusion (auxiliaryWeight n e p) (auxiliaryWeight_measurable n e p)
    (fun m K => auxiliaryWeight_ge_one n m e p he K)
    (fun m tau K => auxiliaryWeight_permutation n m e p tau K)

def auxiliaryHighProjection (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    AuxiliaryFullEnergy n e p he →L[ℂ] AuxiliaryFullEnergy n e p he :=
  (auxiliaryWeightedCoordinates n e p he).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((highSectorProjection n).comp
      (auxiliaryWeightedCoordinates n e p he).toLinearIsometry.toContinuousLinearMap)

theorem auxiliaryHighProjection_physical (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (u : AuxiliaryFullEnergy n e p he) :
    auxiliaryFullEmbedding n e p he (auxiliaryHighProjection n e p he u) =
      highSectorProjection n (auxiliaryFullEmbedding n e p he u) := by
  let G := fockWeightSectorGraph (auxiliaryWeight n e p) (auxiliaryWeight_measurable n e p)
    (fun m K => auxiliaryWeight_ge_one n m e p he K)
    (fun m tau K => auxiliaryWeight_permutation n m e p tau K)
  change sumGraphEmbedding G
    (auxiliaryWeightedCoordinates n e p he
      ((auxiliaryWeightedCoordinates n e p he).symm
        (highSectorProjection n (auxiliaryWeightedCoordinates n e p he u)))) =
      highSectorProjection n (sumGraphEmbedding G (auxiliaryWeightedCoordinates n e p he u))
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply lp.ext
  funext m
  change (G m).embedding ((highSectorProjection n (auxiliaryWeightedCoordinates n e p he u)) m) = _
  rw [highSectorProjection_apply,highSectorProjection_apply]
  by_cases hnm : n ≤ m
  · rw [if_pos hnm,if_pos hnm]
    rfl
  · rw [if_neg hnm,if_neg hnm]
    exact (G m).embedding.map_zero

abbrev AuxiliaryEnergySpace (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :=
  (ContinuousLinearMap.id ℂ (AuxiliaryFullEnergy n e p he) - auxiliaryHighProjection n e p he).ker

theorem auxiliaryEnergy_mem_iff (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (u : AuxiliaryFullEnergy n e p he) :
    u ∈ AuxiliaryEnergySpace n e p he ↔ auxiliaryHighProjection n e p he u = u := by
  change u - auxiliaryHighProjection n e p he u = 0 ↔ auxiliaryHighProjection n e p he u = u
  exact sub_eq_zero.trans eq_comm

def auxiliaryEnergyCoordinates (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    AuxiliaryEnergySpace n e p he ≃ₗᵢ[ℂ] HighSectorSpace n where
  toLinearEquiv :=
    { toFun := fun u => ⟨auxiliaryWeightedCoordinates n e p he u,by
        apply (highSector_mem_iff n _).mpr
        have h := congrArg (auxiliaryWeightedCoordinates n e p he)
          ((auxiliaryEnergy_mem_iff n e p he u).mp u.property)
        change auxiliaryWeightedCoordinates n e p he
          ((auxiliaryWeightedCoordinates n e p he).symm
            (highSectorProjection n (auxiliaryWeightedCoordinates n e p he u))) =
          auxiliaryWeightedCoordinates n e p he u at h
        rw [LinearIsometryEquiv.apply_symm_apply] at h
        exact h⟩
      invFun := fun v => ⟨(auxiliaryWeightedCoordinates n e p he).symm v,by
        apply (auxiliaryEnergy_mem_iff n e p he _).mpr
        change (auxiliaryWeightedCoordinates n e p he).symm
          (highSectorProjection n (auxiliaryWeightedCoordinates n e p he
            ((auxiliaryWeightedCoordinates n e p he).symm v))) =
          (auxiliaryWeightedCoordinates n e p he).symm v
        rw [LinearIsometryEquiv.apply_symm_apply,(highSector_mem_iff n v).mp v.property]⟩
      left_inv := by
        intro u
        apply Subtype.ext
        exact (auxiliaryWeightedCoordinates n e p he).symm_apply_apply u
      right_inv := by
        intro v
        apply Subtype.ext
        exact (auxiliaryWeightedCoordinates n e p he).apply_symm_apply v
      map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
  norm_map' u := (auxiliaryWeightedCoordinates n e p he).norm_map u

def auxiliaryEnergyEmbedding (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    AuxiliaryEnergySpace n e p he →L[ℂ] HighSectorSpace n :=
  ((auxiliaryFullEmbedding n e p he).comp (AuxiliaryEnergySpace n e p he).subtypeL).codRestrict _ (by
    intro u
    apply (highSector_mem_iff n _).mpr
    change highSectorProjection n (auxiliaryFullEmbedding n e p he (u : AuxiliaryFullEnergy n e p he)) =
      auxiliaryFullEmbedding n e p he (u : AuxiliaryFullEnergy n e p he)
    rw [← auxiliaryHighProjection_physical,
      (auxiliaryEnergy_mem_iff n e p he u).mp u.property])

/-- The energy-valued free inverse is an actual onto isometry. -/
def auxiliaryFreeInverseEnergy (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    HighSectorSpace n ≃ₗᵢ[ℂ] AuxiliaryEnergySpace n e p he :=
  (auxiliaryEnergyCoordinates n e p he).symm

end Froehlich
