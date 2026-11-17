import Froehlich.Nodes.FC02
import Froehlich.Nodes.FC01EnergyDensity
import Froehlich.Nodes.EN02Number

/-! FC04: the exact moving energy weight for distinguished-coordinate
annihilation. All stronger field-energy conclusions use free operator inputs. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem totalMomentum_insert_zero (n : ℕ) (k : GW.Space) (K : GW.Fock.Coordinates n) :
    totalMomentum (n+1) ((GW.Fock.splitCoordinates n 0).symm (k,K)) =
      k + totalMomentum n K := by
  unfold totalMomentum
  rw [Fin.sum_univ_succ]
  simp only [GW.Fock.insertCoordinate_same, GW.Fock.insertCoordinate_succAbove]
  rfl

theorem movingEnergyWeight_exact (P k : GW.Space) (n : ℕ) (K : GW.Fock.Coordinates n) :
    energyWeight (P-k) n K ^ 2 =
      freeSymbol P (n+1) ((GW.Fock.splitCoordinates n 0).symm (k,K)) := by
  rw [energyWeight_sq]
  unfold freeSymbol
  rw [totalMomentum_insert_zero]
  have he : totalMomentum n K - (P-k) = k + totalMomentum n K - P := by module
  rw [he]
  push_cast
  ring

theorem movingEnergyWeight_numerical (P k : GW.Space) (n : ℕ) (K : GW.Fock.Coordinates n) :
    (n+1 : ℝ) * energyWeight (P-k) n K ^ 2 ≤
      freeSymbol P (n+1) ((GW.Fock.splitCoordinates n 0).symm (k,K)) ^ 2 := by
  rw [movingEnergyWeight_exact]
  have hn : (n+1 : ℝ) ≤
      freeSymbol P (n+1) ((GW.Fock.splitCoordinates n 0).symm (k,K)) := by
    unfold freeSymbol
    push_cast
    linarith [sq_nonneg ‖totalMomentum (n+1)
      ((GW.Fock.splitCoordinates n 0).symm (k,K)) - P‖]
  simpa only [pow_two] using
    mul_le_mul_of_nonneg_right hn (freeSymbol_nonneg P (n+1) _)

/-- The literal weighted representative to be assembled in Bochner L².
Its definition does not evaluate a class at a prescribed momentum as an
operator: the representative is used only under almost-everywhere statements. -/
def movingEnergySection (P : GW.Space) (n : ℕ)
    (u : GW.Fock.AmbientSector (n+1)) (p : GW.Space × GW.Fock.Coordinates n) : ℂ :=
  (Real.sqrt (n+1 : ℕ) : ℂ) * (energyWeight (P-p.1) n p.2 : ℂ) *
    u ((GW.Fock.splitCoordinates n 0).symm p)

theorem movingEnergySection_norm_sq (P : GW.Space) (n : ℕ)
    (u : GW.Fock.AmbientSector (n+1)) (p : GW.Space × GW.Fock.Coordinates n) :
    ‖movingEnergySection P n u p‖ ^ 2 =
      (n+1 : ℝ) *
        freeSymbol P (n+1) ((GW.Fock.splitCoordinates n 0).symm p) *
          ‖u ((GW.Fock.splitCoordinates n 0).symm p)‖ ^ 2 := by
  unfold movingEnergySection
  rw [norm_mul, norm_mul, mul_pow, mul_pow]
  simp only [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg (zero_le_one.trans (energyWeight_ge_one _ _ _)),
    movingEnergyWeight_exact]
  rw [Real.sq_sqrt (Nat.cast_nonneg (n+1))]
  simp only [Nat.cast_add, Nat.cast_one, Prod.mk.eta]

end Froehlich
