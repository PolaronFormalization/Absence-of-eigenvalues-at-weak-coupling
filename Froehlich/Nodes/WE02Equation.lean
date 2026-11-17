import Froehlich.Nodes.WE02Neumann
import Froehlich.Nodes.OP01Multiplier

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
    (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)

include hCD hquad in
theorem weightedEquation_m_bound (q : GW.Space) :
    ‖thresholdDiagonalMultiplier e he g hg hs q‖ ≤ 1+CD*g^2 := by
  have h := thresholdDiagonalMultiplier_sub_one_bound e he g hg hs CD hCD hquad q
  have ht := abs_add_le (thresholdDiagonalMultiplier e he g hg hs q-1) (1 : ℝ)
  simp only [sub_add_cancel,abs_one] at ht
  have hh : |thresholdDiagonalMultiplier e he g hg hs q-1|+1 ≤ CD*g^2+1 :=
    by simpa only [add_comm] using (add_le_add_right h 1)
  have hfinal := ht.trans hh
  simpa only [Real.norm_eq_abs,add_comm] using hfinal

def weightedEquationMultiplier :
    Lp ℝ ⊤ (volume : Measure GW.Space) →L[ℝ] Lp ℝ ⊤ (volume : Measure GW.Space) :=
  nativeLinftyMultiplier (thresholdDiagonalMultiplier e he g hg hs)
    (thresholdDiagonalMultiplier_measurable e he g hg hs) (1+CD*g^2)
    (Eventually.of_forall (weightedEquation_m_bound e he g hg hs CD hCD hquad))

theorem weightedEquationMultiplier_ae (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    weightedEquationMultiplier e he g hg hs CD hCD hquad f =ᵐ[volume]
      (fun q => thresholdDiagonalMultiplier e he g hg hs q*f q) :=
  nativeLinftyMultiplier_ae _ _ _ _ f

theorem weightedEquationMultiplier_inverse_right (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    weightedEquationMultiplier e he g hg hs CD hCD hquad
      (thresholdInverseLinftyMultiplier e he g hg hs hLower f) = f := by
  apply Lp.ext
  filter_upwards [weightedEquationMultiplier_ae e he g hg hs CD hCD hquad
      (thresholdInverseLinftyMultiplier e he g hg hs hLower f),
    thresholdInverseLinftyMultiplier_ae e he g hg hs hLower f] with q hm hi
  rw [hm,hi,←mul_assoc,mul_inv_cancel₀ (show thresholdDiagonalMultiplier e he g hg hs q ≠ 0 by
    have h := hLower q; linarith),one_mul]

theorem weightedEquationMultiplier_inverse_left (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    thresholdInverseLinftyMultiplier e he g hg hs hLower
      (weightedEquationMultiplier e he g hg hs CD hCD hquad f) = f := by
  apply Lp.ext
  filter_upwards [thresholdInverseLinftyMultiplier_ae e he g hg hs hLower
      (weightedEquationMultiplier e he g hg hs CD hCD hquad f),
    weightedEquationMultiplier_ae e he g hg hs CD hCD hquad f] with q hi hm
  rw [hi,hm,←mul_assoc,inv_mul_cancel₀ (show thresholdDiagonalMultiplier e he g hg hs q ≠ 0 by
    have h := hLower q; linarith),one_mul]

variable (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

def weightedEquationOperator :
    Lp ℝ ⊤ (volume : Measure GW.Space) →L[ℝ] Lp ℝ ⊤ (volume : Measure GW.Space) :=
  weightedEquationMultiplier e he g hg hs CD hCD hquad+
    (g^2) • weightedKernelOperator e he g hg hs P hP

theorem weightedEquation_iff_normalized (z : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    weightedEquationOperator e he g hg hs CD hCD hquad P hP z = weightedKernelSource e he g hg hs P hP ↔
    (1+weightedEquationPerturbation e he g hg hs hLower P hP) z =
      thresholdInverseLinftyMultiplier e he g hg hs hLower (weightedKernelSource e he g hg hs P hP) := by
  let M := weightedEquationMultiplier e he g hg hs CD hCD hquad
  let I := thresholdInverseLinftyMultiplier e he g hg hs hLower
  let L := weightedKernelOperator e he g hg hs P hP
  have hIM (f) : I (M f) = f := weightedEquationMultiplier_inverse_left e he g hg hs hLower CD hCD hquad f
  have hMI (f) : M (I f) = f := weightedEquationMultiplier_inverse_right e he g hg hs hLower CD hCD hquad f
  change M z+g^2 • L z = _ ↔ z+g^2 • I (L z) = _
  constructor
  · intro h
    have hi := congrArg I h
    simpa only [map_add,map_smul,hIM] using hi
  · intro h
    have hm := congrArg M h
    have hMIchi : M (thresholdInverseLinftyMultiplier e he g hg hs hLower
        (weightedKernelSource e he g hg hs P hP)) = weightedKernelSource e he g hg hs P hP :=
      weightedEquationMultiplier_inverse_right e he g hg hs hLower CD hCD hquad _
    have hm' : M z+g^2 • L z = M (thresholdInverseLinftyMultiplier e he g hg hs hLower
        (weightedKernelSource e he g hg hs P hP)) := by
      simpa only [map_add,map_smul,hMI] using hm
    exact hm'.trans hMIchi

variable (hSmall : ‖weightedEquationPerturbation e he g hg hs hLower P hP‖ ≤ 1/2)

include hSmall in
theorem weightedEquationSolution_equation :
    weightedEquationOperator e he g hg hs CD hCD hquad P hP
      (weightedEquationSolution e he g hg hs hLower P hP) = weightedKernelSource e he g hg hs P hP :=
  (weightedEquation_iff_normalized e he g hg hs hLower CD hCD hquad P hP _).mpr
    (weightedEquationSolution_normalized e he g hg hs hLower P hP hSmall)

include hSmall in
theorem weightedEquationSolution_unique (z : Lp ℝ ⊤ (volume : Measure GW.Space))
    (hz : weightedEquationOperator e he g hg hs CD hCD hquad P hP z = weightedKernelSource e he g hg hs P hP) :
    z = weightedEquationSolution e he g hg hs hLower P hP := by
  let T := 1+weightedEquationPerturbation e he g hg hs hLower P hP
  let N := weightedEquationNormalizedInverse e he g hg hs hLower P hP
  have hleft : Function.LeftInverse N T := by
    intro f
    have hp := (weightedEquationNormalizedInverse_spec e he g hg hs hLower P hP hSmall).1
    exact (mul_apply_eq_comp N T f).symm.trans
      ((congrArg (fun A : Lp ℝ ⊤ (volume : Measure GW.Space) →L[ℝ] Lp ℝ ⊤ (volume : Measure GW.Space) => A f) hp).trans
        (ContinuousLinearMap.one_apply f))
  apply hleft.injective
  exact ((weightedEquation_iff_normalized e he g hg hs hLower CD hCD hquad P hP z).mp hz).trans
    (weightedEquationSolution_normalized e he g hg hs hLower P hP hSmall).symm

end Froehlich
