import Froehlich.Nodes.SP03BlockForm
import Froehlich.Nodes.SP03BlockOneRow

/-! The source block solution satisfies the full original energy equation. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (g e eps : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (heLower : -sectorEnergyConstant*|g|^2 ≤ e) (he : e ≤ 0)
    (heps : 0 < eps) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8)
    (hd : 1/2 ≤ onePhononVacuumDenominator e eps P)
    (hd0 : 1/2 ≤ onePhononVacuumDenominator e 0 P)
    (hc : onePhononCorrectionConstant*|g|^2 ≤ 1/2)
    (hzero : ∀ f : OneParticleEnergySpace P,
      0 ≤ (inner ℂ f (onePhononSchurOperator g e 0 P hg heLower he (by norm_num) hsmall hd0 f)).re)

theorem onePhononFullEnergyInverse_right_apply (q : EnergySpace P) :
    vacuumEnergyOperator g P (e+1-eps) (onePhononFullEnergyInverse g e eps P hg heLower he heps hsmall hd hd0 hc hzero q) = q := by
  let c := onePhononEliminationSolveVacuum g e eps P hg heLower he heps hsmall hd hd0 hc hzero q
  let f := onePhononEliminationSolveOne g e eps P hg heLower he heps hsmall hd hd0 hc hzero q
  let z := onePhononEliminationSolveHigh g e eps P hg heLower he heps hsmall hd hd0 hc hzero q
  have hj : onePhononFullEnergyInverse g e eps P hg heLower he heps hsmall hd hd0 hc hzero q = onePhononEnergyJoin P c f z := rfl
  rw [hj]
  apply onePhononBlockForm_test_ext
  · rw [onePhononBlockForm_vacuum_row]
    have hcoef : ((‖P‖^2-(e+1-eps) : ℝ) : ℂ) = -((onePhononVacuumDenominator e eps P : ℝ) : ℂ) := by
      rw [← Complex.ofReal_neg]
      congr 1
      unfold onePhononVacuumDenominator
      ring
    have hv := onePhononEliminationSolveVacuum_equation g e eps P hg heLower he heps hsmall hd hd0 hc hzero q
    change -((onePhononVacuumDenominator e eps P : ℝ) : ℂ)*c + onePhononSourceLinear g P f =
      (vacuumEnergyInclusion P).adjoint q at hv
    have hload : (vacuumEnergyInclusion P).adjoint q = ⟪vacuumEnergyLift P,q⟫_ℂ := by
      have h := (vacuumEnergyInclusion P).adjoint_inner_right (1 : ℂ) q
      have hinc : vacuumEnergyInclusion P (1 : ℂ) = vacuumEnergyLift P := by
        simp [vacuumEnergyInclusion]
      rw [hinc] at h
      simpa using h
    rw [hcoef,hv,hload]
  · intro h
    rw [onePhononBlockForm_one_row]
    have ho := onePhononEliminationSolveOne_full_equation g e eps P hg heLower he heps hsmall hd hd0 hc hzero q
    change f + ((eps-e-1 : ℝ) : ℂ) • onePhononMassOperator P f +
      (onePhononSourceLinear g P).adjoint c + (twoSectorCoupling g P).adjoint z =
        (onePhononEnergyLift P).adjoint q at ho
    have hs : -((e+1-eps : ℝ) : ℂ) = ((eps-e-1 : ℝ) : ℂ) := by
      push_cast
      ring
    have hv : (onePhononSourceLinear g P).adjoint c +
        (1-((e+1-eps : ℝ) : ℂ) • onePhononMassOperator P) f +
          (twoSectorCoupling g P).adjoint z = (onePhononEnergyLift P).adjoint q := by
      have hn : -(((e+1-eps : ℝ) : ℂ) • onePhononMassOperator P f) =
          ((eps-e-1 : ℝ) : ℂ) • onePhononMassOperator P f :=
        (neg_smul ((e+1-eps : ℝ) : ℂ) (onePhononMassOperator P f)).symm.trans
          (congrArg (fun r : ℂ => r • onePhononMassOperator P f) hs)
      have hdiag : (1-((e+1-eps : ℝ) : ℂ) • onePhononMassOperator P) f =
          f + ((eps-e-1 : ℝ) : ℂ) • onePhononMassOperator P f := by
        calc
          _ = f - ((e+1-eps : ℝ) : ℂ) • onePhononMassOperator P f := rfl
          _ = f + -(((e+1-eps : ℝ) : ℂ) • onePhononMassOperator P f) := sub_eq_add_neg _ _
          _ = _ := congrArg (fun y : OneParticleEnergySpace P => f+y) hn
      have heq := congrArg (fun y : OneParticleEnergySpace P =>
        (onePhononSourceLinear g P).adjoint c + y + (twoSectorCoupling g P).adjoint z) hdiag
      exact heq.trans (by
        calc
          _ = f + ((eps-e-1 : ℝ) : ℂ) • onePhononMassOperator P f +
              (onePhononSourceLinear g P).adjoint c + (twoSectorCoupling g P).adjoint z := by abel
          _ = _ := ho)
    rw [hv,(onePhononEnergyLift P).adjoint_inner_right]
  · intro w
    rw [onePhononBlockForm_high_row]
    have hh := onePhononEliminationSolveHigh_equation g e eps P hg heLower he heps hsmall hd hd0 hc hzero q
    change twoSectorOperator g P (e+1-eps) z + twoSectorCoupling g P f =
      (HighEnergySpace P 2).subtypeL.adjoint q at hh
    have hh' : twoSectorCoupling g P f + twoSectorOperator g P (e+1-eps) z =
        (HighEnergySpace P 2).subtypeL.adjoint q := by simpa only [add_comm] using hh
    rw [hh',(HighEnergySpace P 2).subtypeL.adjoint_inner_right]
    rfl

end Froehlich
