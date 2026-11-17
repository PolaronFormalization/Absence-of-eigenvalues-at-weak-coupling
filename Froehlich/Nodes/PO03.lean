import Froehlich.Nodes.WE06
import Froehlich.Nodes.PO03Application
import Froehlich.Nodes.PO03ScalarCriterion
import Froehlich.Nodes.PO02
import Froehlich.Nodes.KE02ConstantQuadratic

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

/-- One positive cutoff gives positivity of the actual untranslated threshold form
on its complete form domain, including zero momentum. -/
theorem finalPO03 : ∃ s : ℝ, 0 < s ∧
    ∀ g : ℝ, g ≠ 0 → |g| < s →
      ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
      ∃ hquarter : |g| ≤ 1/4,
      ∃ heLower : -sectorEnergyConstant*|g|^2 ≤ groundEnergy (fiberHamiltonian g 0),
      ∃ hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8,
      ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4) (f : OneParticleEnergySpace P),
        0 ≤ (untranslatedThresholdForm (groundEnergy (fiberHamiltonian g 0)) he g
          hquarter heLower hquadratic P hP f f).re := by
  obtain ⟨CU,CT,CN,CW,CD,sW,hCU,hCT,hCN,hCW,hCD,hsW,hW⟩ := finalWE06
  obtain ⟨CK,hCK,hK⟩ := kernelConstant_quadratic_uniform
  obtain ⟨sT,hsT,hT⟩ := pt03_ground_reference_smallness
  obtain ⟨sA,hsA,hA⟩ := auxiliarySelfEnergy_zero_groundEnergy
  obtain ⟨sZ,hsZ,hZ⟩ := finalPO02
  let C := max 1 (max CK (max CU (max CT CN)))
  have hC : 1 ≤ C := le_max_left _ _
  have hCKC : CK ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCUC : CU ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCTC : CT ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))
  have hCNC : CN ≤ C := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let s := min sW (min sT (min sA (min sZ (1/(4*C)))))
  refine ⟨s,lt_min hsW (lt_min hsT (lt_min hsA (lt_min hsZ (by positivity)))),?_⟩
  intro g hg0 hgs
  have hgW : |g| < sW := hgs.trans_le (min_le_left _ _)
  have hgRest := hgs.trans_le (min_le_right sW _)
  have hgT : |g| < sT := hgRest.trans_le (min_le_left _ _)
  have hgRest' := hgRest.trans_le (min_le_right sT _)
  have hgA : |g| < sA := hgRest'.trans_le (min_le_left _ _)
  have hgRest'' := hgRest'.trans_le (min_le_right sA _)
  have hgZ : |g| < sZ := hgRest''.trans_le (min_le_left _ _)
  have hgC : |g| < 1/(4*C) := hgRest''.trans_le (min_le_right _ _)
  obtain ⟨he,hg,haux,hCD0,hquad,hLower,_hWeighted,hRef⟩ := hW g hgW
  obtain ⟨_heT,_hgT,_hauxT,hquarter,heLower,hquadratic⟩ := hT g hgT
  obtain ⟨_heA,_hgA,_hauxA,hanchor⟩ := hA g hgA
  have hSat : thresholdScalarN _ he g hg haux CD hCD0 hquad 0 (by simp) =
      kernelConstant _ he g hg haux 0 := by
    simpa only [thresholdScalarN,Complex.ofReal_re] using congrArg Complex.re
      (se03_saturation _ he g hg haux CD hCD0 hquad hquarter heLower hquadratic
        hanchor (hRef.1 0 (by simp)) hg0)
  have hCa : C*|g| ≤ 1/4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4*C)).mp hgC.le
    nlinarith only [h]
  refine ⟨he,hquarter,heLower,hquadratic,?_⟩
  intro P hP f
  have htranslated : ∀ v : OneParticleEnergySpace 0,
      0 ≤ (translatedThresholdForm _ he g hquarter heLower hquadratic P hP v v).re := by
    by_cases hP0 : P = 0
    · subst P
      obtain ⟨_heZ,_hquarterZ,_heLowerZ,_hquadraticZ,hzero⟩ := hZ g hg0 hgZ
      exact hzero
    · have hr : 0 < ‖P‖ := norm_pos_iff.mpr hP0
      obtain ⟨_hIntegral,_hReal,hU,_hTReal,hT0,hTBound⟩ := hRef.2.2.2 P hP hP0
      have hDiff : |kernelConstant _ he g hg haux P-
          thresholdScalarN _ he g hg haux CD hCD0 hquad P hP| ≤ C*(‖P‖^2+|g|^2*‖P‖) := by
        calc
          _ = |(kernelConstant _ he g hg haux P-kernelConstant _ he g hg haux 0)+
              (thresholdScalarN _ he g hg haux CD hCD0 hquad 0 (by simp)-
               thresholdScalarN _ he g hg haux CD hCD0 hquad P hP)| := by rw [hSat]; congr 1; ring
          _ ≤ |kernelConstant _ he g hg haux P-kernelConstant _ he g hg haux 0|+
              |thresholdScalarN _ he g hg haux CD hCD0 hquad 0 (by simp)-
               thresholdScalarN _ he g hg haux CD hCD0 hquad P hP| := abs_add_le _ _
          _ ≤ CK*‖P‖^2+CN*g^2*‖P‖ := add_le_add (hK _ he g hg haux P hP)
            (by simpa only [abs_sub_comm] using hRef.2.2.1 P hP)
          _ ≤ C*‖P‖^2+C*g^2*‖P‖ := add_le_add
            (mul_le_mul_of_nonneg_right hCKC (sq_nonneg _))
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCNC (sq_nonneg g)) hr.le)
          _ = _ := by rw [sq_abs]; ring
      have hU' : ‖thresholdScalarU _ he g hg haux CD hCD0 hquad P hP hP0‖ ≤ C*|g|^2 := by
        rw [sq_abs]
        exact hU.trans (mul_le_mul_of_nonneg_right hCUC (sq_nonneg g))
      have hTr : thresholdScalarT _ he g hg haux CD hCD0 hquad P hP hP0*‖P‖ ≤ C*|g|^2 := by
        rw [sq_abs]
        exact ((le_div_iff₀ hr).mp hTBound).trans (mul_le_mul_of_nonneg_right hCTC (sq_nonneg g))
      have hn := po03_scalar_criterion C |g| ‖P‖
        (thresholdScalarT _ he g hg haux CD hCD0 hquad P hP hP0)
        (kernelConstant _ he g hg haux P-thresholdScalarN _ he g hg haux CD hCD0 hquad P hP)
        (thresholdScalarU _ he g hg haux CD hCD0 hquad P hP hP0)
        hC (abs_nonneg g) hCa hr hP hU' hT0 hTr hDiff
      exact translatedThresholdForm_nonnegative_of_criterion _ he g hg haux CD hCD0 hquad
        hquarter heLower hquadratic P hP hP0 (hRef.1 P hP) hn.1
        ((by norm_num : (0 : ℝ) ≤ 220/256).trans hn.2)
  have ht := htranslated (energyTranslation P f)
  simpa only [translatedThresholdForm,LinearIsometryEquiv.symm_apply_apply] using ht

end Froehlich
