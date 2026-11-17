import Froehlich.Nodes.FB03
import Froehlich.Nodes.FB01KineticIdentityFull
import Froehlich.Nodes.GW06Sectors

/-! Actual high-sector number lower bounds and the source nonvacuum coercivity. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def energyNumberExpectation (P : GW.Space) (u : EnergySpace P) : ℝ :=
  ‖GW.Fock.numberPower GW.Fock.Sector (1/2)
    (numberFormRootInput (energyNumberCoordinates P u))‖^2

theorem highEnergy_number_lower (P : GW.Space) (m : ℕ) (u : HighEnergySpace P m) :
    (m : ℝ)*‖energyEmbedding P (u : EnergySpace P)‖^2 ≤ energyNumberExpectation P u := by
  let v := energyEmbedding P (u : EnergySpace P)
  have hv : highSectorProjection m v = v := by
    rw [← energyHighProjection_intertwines]
    exact congrArg (energyEmbedding P) ((highEnergy_mem_iff P m (u : EnergySpace P)).mp u.property)
  have hs := (GW.Analysis.memℓp_two_iff_sq _).mp v.property
  have hN := numberFormRoot_summable (energyNumberCoordinates P (u : EnergySpace P))
  rw [energyNumberCoordinates_intertwines] at hN
  change (m : ℝ)*‖v‖^2 ≤ _
  rw [GW.Fock.carrier_norm_sq]
  change (m : ℝ)*(∑' n : ℕ, ‖v n‖^2) ≤
    ‖GW.Fock.numberPower GW.Fock.Sector (1/2)
      (numberFormRootInput (energyNumberCoordinates P (u : EnergySpace P)))‖^2
  rw [numberFormRoot_norm,energyNumberCoordinates_intertwines]
  have hterms : ∀ n : ℕ, (m : ℝ)*‖v n‖^2 ≤ (n : ℝ)*‖v n‖^2 := by
    intro n
    by_cases hn : m ≤ n
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (sq_nonneg ‖v n‖)
    · have he := congrArg (fun z : GW.Fock.Carrier => z n) hv
      rw [highSectorProjection_apply,if_neg hn] at he
      have hz : v n = 0 := he.symm
      simp [hz]
  have hNs : Summable (fun n : ℕ => (n : ℝ)*‖v n‖^2) := hN
  calc
    _ = ∑' n : ℕ, (m : ℝ)*‖v n‖^2 := (hs.tsum_mul_left (m : ℝ)).symm
    _ ≤ ∑' n : ℕ, (n : ℝ)*‖v n‖^2 :=
      Summable.tsum_le_tsum hterms (hs.mul_left (m : ℝ)) hNs

theorem fiberForm_nonvacuum_lower (g lam : ℝ) (P : GW.Space) (u : HighEnergySpace P 1)
    (hg : |g| ≤ 1/4) :
    (1-|g|)*energyKineticNorm P u ^ 2 +
      (1-|g|)*(energyNumberExpectation P u - ‖energyEmbedding P (u : EnergySpace P)‖^2) +
      (nonvacuumThreshold g-lam)*‖energyEmbedding P (u : EnergySpace P)‖^2 ≤
      ((fiberFormData g P none).form u u).re - lam*‖energyEmbedding P (u : EnergySpace P)‖^2 := by
  have h := fiberForm_linear_lower g P (u : EnergySpace P) hg
  have he := energyKineticNorm_number_identity P (u : EnergySpace P)
  change energyKineticNorm P u ^ 2 + energyNumberExpectation P u = _ at he
  dsimp only [nonvacuumThreshold,sectorLinearConstant]
  nlinarith

theorem fiberForm_nonvacuum_coercive (g lam : ℝ) (P : GW.Space) (u : HighEnergySpace P 1)
    (hg : |g| ≤ 1/4) (hlam : lam < nonvacuumThreshold g) :
    min (1-|g|) ((nonvacuumThreshold g-lam)/2) * ‖u‖^2 ≤
      ((fiberFormData g P none).form u u).re - lam*‖energyEmbedding P (u : EnergySpace P)‖^2 := by
  let a := min (1-|g|) ((nonvacuumThreshold g-lam)/2)
  have h1 : a ≤ 1-|g| := min_le_left _ _
  have h2 : 2*a ≤ nonvacuumThreshold g-lam := by dsimp [a]; linarith [min_le_right (1-|g|) ((nonvacuumThreshold g-lam)/2)]
  have hN := highEnergy_number_lower P 1 u
  simp only [Nat.cast_one,one_mul] at hN
  have hn : ‖u‖^2 = ‖energyEmbedding P (u : EnergySpace P)‖^2 +
      freeEnergy P (energyEmbedding P (u : EnergySpace P)) :=
    energyEmbedding_norm_identity P (u : EnergySpace P)
  have he := energyKineticNorm_number_identity P (u : EnergySpace P)
  change energyKineticNorm P u ^ 2 + energyNumberExpectation P u = _ at he
  have hk := mul_le_mul_of_nonneg_right h1 (sq_nonneg (energyKineticNorm P u))
  have hnum := mul_le_mul_of_nonneg_right h1 (sub_nonneg.mpr hN)
  have hm := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖energyEmbedding P (u : EnergySpace P)‖)
  have hb := fiberForm_nonvacuum_lower g lam P u hg
  change a*‖u‖^2 ≤ _
  nlinarith

theorem nonvacuum_coercivity_positive (g lam : ℝ) (hg : |g| ≤ 1/4)
    (hlam : lam < nonvacuumThreshold g) :
    0 < min (1-|g|) ((nonvacuumThreshold g-lam)/2) := by
  exact lt_min (by linarith) (by linarith)

end Froehlich
