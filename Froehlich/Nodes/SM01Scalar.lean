import Froehlich.Nodes.SM01Absorption
import Froehlich.Nodes.WE06
import Froehlich.Nodes.PO03ScalarCriterion
import Froehlich.Nodes.KE02

set_option autoImplicit false
noncomputable section
namespace Froehlich

/-- The literal final SM01 scalar margin, on actual model scalars under the ordered ledger. -/
theorem sm01_actual_scalar_margin (I K : ℝ) (hI : 1 ≤ I) (hK : 1 ≤ K)
    (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
    (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (hWeighted : WE06FixedReference (sm01CU I K) (sm01CT I K) (sm01CN I K)
      CD e he g hg hs hLower hCD hquad)
    (hKernel : KE02FixedReference K e he g hg hs)
    (hSat : thresholdScalarN e he g hg hs CD hCD hquad 0 (by simp) = kernelConstant e he g hg hs 0)
    (hCa : sm01CommonC I K*|g| ≤ 1/4) :
    ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4) (hP0 : P ≠ 0),
      1+thresholdScalarU e he g hg hs CD hCD hquad P hP hP0 ≠ 0 ∧
      (220/256 : ℝ) ≤ ‖1+thresholdScalarU e he g hg hs CD hCD hquad P hP hP0‖^2+
        thresholdScalarT e he g hg hs CD hCD hquad P hP hP0*
          (kernelConstant e he g hg hs P-thresholdScalarN e he g hg hs CD hCD hquad P hP) := by
  let C := sm01CommonC I K
  obtain ⟨hC,hKC,hUC,hTC,hNC⟩ := sm01CommonC_dominance I K
  intro P hP hP0
  have hr : 0 < ‖P‖ := norm_pos_iff.mpr hP0
  obtain ⟨_hIntegral,_hReal,hU,_hTReal,hT0,hTBound⟩ := hWeighted.2.2.2 P hP hP0
  have hDiff : |kernelConstant e he g hg hs P-thresholdScalarN e he g hg hs CD hCD hquad P hP| ≤
      C*(‖P‖^2+|g|^2*‖P‖) := by
    calc
      _ = |(kernelConstant e he g hg hs P-kernelConstant e he g hg hs 0)+
          (thresholdScalarN e he g hg hs CD hCD hquad 0 (by simp)-
            thresholdScalarN e he g hg hs CD hCD hquad P hP)| := by rw [hSat]; congr 1; ring
      _ ≤ |kernelConstant e he g hg hs P-kernelConstant e he g hg hs 0|+
          |thresholdScalarN e he g hg hs CD hCD hquad 0 (by simp)-
            thresholdScalarN e he g hg hs CD hCD hquad P hP| := abs_add_le _ _
      _ ≤ K*‖P‖^2+sm01CN I K*g^2*‖P‖ := add_le_add (hKernel.1 P hP).1
        (by simpa only [abs_sub_comm] using hWeighted.2.2.1 P hP)
      _ ≤ C*‖P‖^2+C*g^2*‖P‖ := add_le_add
        (mul_le_mul_of_nonneg_right hKC (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNC (sq_nonneg g)) hr.le)
      _ = _ := by rw [sq_abs]; ring
  have hU' : ‖thresholdScalarU e he g hg hs CD hCD hquad P hP hP0‖ ≤ C*|g|^2 := by
    rw [sq_abs]
    exact hU.trans (mul_le_mul_of_nonneg_right hUC (sq_nonneg g))
  have hTr : thresholdScalarT e he g hg hs CD hCD hquad P hP hP0*‖P‖ ≤ C*|g|^2 := by
    rw [sq_abs]
    exact ((le_div_iff₀ hr).mp hTBound).trans (mul_le_mul_of_nonneg_right hTC (sq_nonneg g))
  exact po03_scalar_criterion C |g| ‖P‖
    (thresholdScalarT e he g hg hs CD hCD hquad P hP hP0)
    (kernelConstant e he g hg hs P-thresholdScalarN e he g hg hs CD hCD hquad P hP)
    (thresholdScalarU e he g hg hs CD hCD hquad P hP hP0)
    hC (abs_nonneg g) hCa hr hP hU' hT0 hTr hDiff

end Froehlich
