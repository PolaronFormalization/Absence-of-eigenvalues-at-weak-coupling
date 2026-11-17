import Froehlich.Nodes.SM01Absorption
import Froehlich.Nodes.SM01ConstantMonotonic
import Froehlich.Nodes.SM01Weighted
import Froehlich.Nodes.SM01Scalar
import Froehlich.Nodes.PO03

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

/-- The source's six-entry preliminary range, with the literal physical constants. -/
def sm01PhysicalPreCutoff : ℝ := sm01PreCutoff sectorEnergyConstant sectorLinearConstant
  sectorQuadraticConstant auxiliaryResolventConstant onePhononCorrectionConstant

def sm01CouplingCutoff (I K Cm : ℝ) : ℝ :=
  sm01FinalCutoff (sm01AuxCutoff sm01PhysicalPreCutoff Cm K I) I K

def SM01NumericalGuards (g : ℝ) : Prop :=
  |g| ≤ 1/4 ∧ sectorLinearConstant*|g| ≤ 1/8 ∧ sectorEnergyConstant*|g|^2 ≤ 1/8 ∧
  sectorQuadraticConstant*|g|^2 ≤ 1/8 ∧ auxiliaryResolventConstant*|g| ≤ 1/2 ∧
  onePhononCorrectionConstant*|g|^2 ≤ 1/2

/-- All objects here are the actual full-domain fiber Hamiltonian and its real spectrum. -/
def SM01AuxiliaryGuards (I K Cm g : ℝ) : Prop :=
  Cm*|g|^2 ≤ 1/4 ∧ (Cm+K*I)*|g|^2 ≤ 1/2 ∧
  (4/3 : ℝ)*|g|^2*K*I ≤ 1/2 ∧ sm01CommonC I K*|g| ≤ 1/4 ∧
  sm01CommonC I K*|g|^2 ≤ 1/16

def SM01VacuumData (g : ℝ) (P : GW.Space) : Prop :=
  groundEnergy (fiberHamiltonian g P) ≤ ‖P‖^2 ∧
  -sectorEnergyConstant*|g|^2 ≤ groundEnergy (fiberHamiltonian g P) ∧
  realSpectrum (fiberHamiltonian g P) ∩ Set.Iio (nonvacuumThreshold g) =
    {groundEnergy (fiberHamiltonian g P)} ∧
  HasEigenvector (fiberHamiltonian g P) (groundEnergy (fiberHamiltonian g P))

def SM01PositivityData (g : ℝ) : Prop :=
  ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
  ∃ hquarter : |g| ≤ 1/4,
  ∃ heLower : -sectorEnergyConstant*|g|^2 ≤ groundEnergy (fiberHamiltonian g 0),
  ∃ hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8,
  ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4) (f : OneParticleEnergySpace P),
    0 ≤ (untranslatedThresholdForm (groundEnergy (fiberHamiltonian g 0)) he g
      hquarter heLower hquadratic P hP f f).re

/-- The source's explicit comparison constants bound the actual weighted solutions. -/
def SM01ExplicitWeightedBounds (I K e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q) : Prop :=
  (∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
    ‖weightedEquationSolution e he g hg hs hLower P hP‖ ≤ sm01CEta I K) ∧
  (∀ q : GW.Space, |weightedEtaIntegral e he g hg hs 0
    (weightedEquationEta e he g hg hs hLower 0 (by simp)) q| ≤ sm01CJ I K*(omega q)^2) ∧
  (∀ q : GW.Space, |weightedEquationEtaPrime e he g hg hs 0 hLower (by simp) q| ≤ sm01CZero I K*(omega q)^2) ∧
  (∀ᵐ q ∂volume, |weightedEquationEta e he g hg hs hLower 0 (by simp) q| ≤ sm01CZero I K*(omega q)^2) ∧
  (∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
    ‖weightedEquationSolution e he g hg hs hLower P hP-
      weightedEquationSolution e he g hg hs hLower 0 (by simp)‖ ≤ sm01CDelta I K*‖P‖) ∧
  ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4), ∀ᵐ q ∂volume,
    |weightedEquationEta e he g hg hs hLower P hP q-
      weightedEquationEta e he g hg hs hLower 0 (by simp) q| ≤ sm01CDelta I K*‖P‖*omega q ∧
    |weightedEquationEta e he g hg hs hLower P hP q| ≤ sm01CSharp I K*omega q*(omega q+‖P‖)

/-- The three operator/source bounds in the source's second range. -/
def SM01OperatorBounds (I K e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) : Prop :=
  ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
    ‖thresholdIntegralOperator e he g hg hs P hP‖ ≤ K*I ∧
    ‖weightedKernelOperator e he g hg hs P hP‖ ≤ K*I ∧
    ‖weightedKernelSource e he g hg hs P hP‖ ≤ 2*K

def SM01WeightedData (I K Cm CW CD g : ℝ) : Prop :=
  ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
  ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
  ∃ hCD : 0 ≤ CD,
  ∃ hquad : ∀ q : GW.Space,
    |auxiliarySelfEnergy (groundEnergy (fiberHamiltonian g 0)) q he g hg hs-
      groundEnergy (fiberHamiltonian g 0)| ≤ CD*g^2*‖q‖^2,
  ∃ hLower : ∀ q : GW.Space,
    3/4 ≤ thresholdDiagonalMultiplier (groundEnergy (fiberHamiltonian g 0)) he g hg hs q,
  (∀ q : GW.Space, |thresholdDiagonalMultiplier (groundEnergy (fiberHamiltonian g 0)) he g hg hs q-1| ≤ Cm*g^2) ∧
  WE02FixedReference CW CD (groundEnergy (fiberHamiltonian g 0)) he g hg hs hCD hquad hLower ∧
  WE06FixedReference (sm01CU I K) (sm01CT I K) (sm01CN I K) CD
    (groundEnergy (fiberHamiltonian g 0)) he g hg hs hLower hCD hquad ∧
  SM01ExplicitWeightedBounds I K (groundEnergy (fiberHamiltonian g 0)) he g hg hs hLower ∧
  SM01OperatorBounds I K (groundEnergy (fiberHamiltonian g 0)) he g hg hs ∧
  (g ≠ 0 → ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4) (hP0 : P ≠ 0),
    1+thresholdScalarU _ he g hg hs CD hCD hquad P hP hP0 ≠ 0 ∧
    (220/256 : ℝ) ≤ ‖1+thresholdScalarU _ he g hg hs CD hCD hquad P hP hP0‖^2+
      thresholdScalarT _ he g hg hs CD hCD hquad P hP hP0*
        (kernelConstant _ he g hg hs P-thresholdScalarN _ he g hg hs CD hCD hquad P hP))

/-- Finite ordered selection. I and K are enlarged uniform witnesses first;
Cm is then enlarged by explicit finite absorption. This keeps the exact source
s_pre, s_aux, comparison-constant, and final-cutoff formulas, without an extra
minimum in g_star or any coupling-dependent choice of constants. -/
theorem finalSM01 : ∃ I K Cm CW CD : ℝ,
    1 ≤ I ∧ 1 ≤ K ∧ 0 ≤ Cm ∧ 0 < CW ∧ 0 < CD ∧
    SM01IntegralConstant I ∧
    (∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2), KE02FixedReference K e he g hg hs) ∧
    0 < sm01CouplingCutoff I K Cm ∧
    ∀ g : ℝ, |g| < sm01CouplingCutoff I K Cm →
      SM01NumericalGuards g ∧ SM01AuxiliaryGuards I K Cm g ∧
      (7/8 : ℝ) ≤ nonvacuumThreshold g ∧
      -(1/8 : ℝ) ≤ groundEnergy (fiberHamiltonian g 0) ∧
      groundEnergy (fiberHamiltonian g 0) ≤ 0 ∧
      (∀ (P : GW.Space), ‖P‖ ≤ 1/4 → SM01VacuumData g P) ∧
      SM01WeightedData I K Cm CW CD g ∧
      (g ≠ 0 → SM01PositivityData g) := by
  obtain ⟨CU,CT,CN,CW,CD,sW,hCU,hCT,hCN,hCW,hCD,hsW,hW⟩ := finalWE06
  obtain ⟨CI,hCI,hIntegral⟩ := sm01_integralConstant_exists
  obtain ⟨KK,hKK,hKernel⟩ := finalKE02_uniform
  obtain ⟨CJ,hCJ,hJ⟩ := weightedEquationEta_integral_zero_quadratic
  obtain ⟨CZ,hCZ,hZero⟩ := weightedEquationEta_zero_quadratic_uniform
  obtain ⟨CDelta,hCDelta,hDelta⟩ := weightedEquationSolution_comparison_uniform
  obtain ⟨CE,hCE,hEta⟩ := weightedEquationEta_comparison_uniform
  obtain ⟨CKop,hCKop,hKop⟩ := thresholdIntegralOperator_norm_uniform
  obtain ⟨CLop,hCLop,hLop⟩ := weightedKernelOperator_norm_uniform
  obtain ⟨CChi,hCChi,hChi⟩ := weightedKernelSource_norm_uniform
  obtain ⟨sSP,hsSP,hSP⟩ := finalSP01
  obtain ⟨sPos,hsPos,hPos⟩ := finalPO03
  let I := max 1 (CI+CT)
  let K := max 1 (KK+CU+CN+CW+CJ+CZ+CDelta+CE+CKop+CLop+CChi)
  have hI : 1 ≤ I := le_max_left _ _
  have hK : 1 ≤ K := le_max_left _ _
  have hCII : CI ≤ I := (by linarith : CI ≤ CI+CT).trans (le_max_right _ _)
  have hCTI : CT ≤ I := (by linarith : CT ≤ CI+CT).trans (le_max_right _ _)
  have hKKK : KK ≤ K := (by linarith : KK ≤ KK+CU+CN+CW+CJ+CZ+CDelta+CE+CKop+CLop+CChi).trans (le_max_right _ _)
  have hCUK : CU ≤ K := (by linarith : CU ≤ KK+CU+CN+CW+CJ+CZ+CDelta+CE+CKop+CLop+CChi).trans (le_max_right _ _)
  have hCNK : CN ≤ K := (by linarith : CN ≤ KK+CU+CN+CW+CJ+CZ+CDelta+CE+CKop+CLop+CChi).trans (le_max_right _ _)
  have hCWK : CW ≤ K := (by linarith : CW ≤ KK+CU+CN+CW+CJ+CZ+CDelta+CE+CKop+CLop+CChi).trans (le_max_right _ _)
  have hCJK : CJ ≤ K := (by linarith : CJ ≤ KK+CU+CN+CW+CJ+CZ+CDelta+CE+CKop+CLop+CChi).trans (le_max_right _ _)
  have hCZK : CZ ≤ K := (by linarith : CZ ≤ KK+CU+CN+CW+CJ+CZ+CDelta+CE+CKop+CLop+CChi).trans (le_max_right _ _)
  have hCDeltaK : CDelta ≤ K := (by linarith : CDelta ≤ KK+CU+CN+CW+CJ+CZ+CDelta+CE+CKop+CLop+CChi).trans (le_max_right _ _)
  have hCEK : CE ≤ K := (by linarith : CE ≤ KK+CU+CN+CW+CJ+CZ+CDelta+CE+CKop+CLop+CChi).trans (le_max_right _ _)
  have hCKopK : CKop ≤ K := (by linarith : CKop ≤ KK+CU+CN+CW+CJ+CZ+CDelta+CE+CKop+CLop+CChi).trans (le_max_right _ _)
  have hCLopK : CLop ≤ K := (by linarith : CLop ≤ KK+CU+CN+CW+CJ+CZ+CDelta+CE+CKop+CLop+CChi).trans (le_max_right _ _)
  have hCChiK : CChi ≤ K := (by linarith : CChi ≤ KK+CU+CN+CW+CJ+CZ+CDelta+CE+CKop+CLop+CChi).trans (le_max_right _ _)
  let sigma := min sW (min sSP sPos)
  have hsigma : 0 < sigma := lt_min hsW (lt_min hsSP hsPos)
  obtain ⟨Cm,hCDCm,hCm,_hAbsorb,hAuxSigma⟩ := sm01_finite_absorption sigma CD hsigma hCD.le
  have hC2 : 0 ≤ sectorQuadraticConstant := by
    unfold sectorQuadraticConstant
    exact mul_nonneg (by norm_num) lySmallConstant_pos.le
  have hC1 : 0 ≤ sectorLinearConstant := by
    have hL := lySmallConstant_pos
    unfold sectorLinearConstant
    linarith
  have hCorrection : 0 ≤ onePhononCorrectionConstant := by unfold onePhononCorrectionConstant; positivity
  have hPre : 0 < sm01PhysicalPreCutoff := sm01PreCutoff_pos _ _ _ _ _
    sectorEnergyConstant_pos.le hC1 hC2 auxiliaryResolventConstant_pos.le hCorrection
  have hAux : 0 < sm01AuxCutoff sm01PhysicalPreCutoff Cm K I :=
    sm01AuxCutoff_pos _ _ _ _ hPre hCm (zero_le_one.trans hK) (zero_le_one.trans hI)
  have hFinal : 0 < sm01CouplingCutoff I K Cm := sm01FinalCutoff_pos _ I K hAux
  refine ⟨I,K,Cm,CW,CD,hI,hK,hCm,hCW,hCD,
    SM01IntegralConstant_mono CI I hCII hIntegral,?_,hFinal,?_⟩
  · intro e he g hg hs
    exact KE02FixedReference_mono KK K e he g hg hs hKKK (hKernel e he g hg hs)
  · intro g hgs
    have hgAux : |g| ≤ sm01AuxCutoff sm01PhysicalPreCutoff Cm K I := by
      have hh : |g| < sm01AuxCutoff sm01PhysicalPreCutoff Cm K I/2 :=
        hgs.trans_le (min_le_left _ _)
      linarith
    have hgSigma : |g| < sigma := by
      have hh : |g| < sm01AuxCutoff sm01PhysicalPreCutoff Cm K I/2 := hgs.trans_le (min_le_left _ _)
      have hle := hAuxSigma sm01PhysicalPreCutoff K I
      linarith
    have hgW : |g| < sW := hgSigma.trans_le (min_le_left _ _)
    have hgSP : |g| < sSP := hgSigma.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hgPos : |g| < sPos := hgSigma.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hauxGuards := sm01AuxCutoff_guards sm01PhysicalPreCutoff Cm K I |g| hCm
      (zero_le_one.trans hK) (zero_le_one.trans hI) (abs_nonneg g) hgAux
    have hgPre : |g| ≤ sm01PhysicalPreCutoff := by linarith [hauxGuards.1]
    have hnum : SM01NumericalGuards g := sm01PreCutoff_guards _ _ _ _ _ |g|
      sectorEnergyConstant_pos.le hC1 hC2 auxiliaryResolventConstant_pos.le hCorrection
      (abs_nonneg g) hgPre
    have hCa : sm01CommonC I K*|g| ≤ 1/4 := by
      have hCpos : 0 < sm01CommonC I K := lt_of_lt_of_le zero_lt_one (sm01CommonC_dominance I K).1
      have hh : |g| ≤ 1/(4*sm01CommonC I K) := hgs.le.trans (min_le_right _ _)
      have hmul := (le_div_iff₀ (by positivity : 0 < 4*sm01CommonC I K)).mp hh
      nlinarith only [hmul]
    have hCaSq : sm01CommonC I K*|g|^2 ≤ 1/16 := by
      have h := mul_le_mul hCa hnum.1 (abs_nonneg g) (by norm_num : (0 : ℝ) ≤ 1/4)
      nlinarith only [h]
    have hAuxNum : SM01AuxiliaryGuards I K Cm g :=
      ⟨hauxGuards.2.1,hauxGuards.2.2.1,hauxGuards.2.2.2,hCa,hCaSq⟩
    have hVac (P : GW.Space) (hP : ‖P‖ ≤ 1/4) : SM01VacuumData g P := by
      obtain ⟨hgc,he,hl,hu,hlo,hr,huniq,hspec,hform,hcan,hcoeff,hneq,hm,hEV⟩ := hSP g hgSP P hP
      refine ⟨hu,?_,hspec,?_⟩
      · simpa only [neg_mul] using hlo
      · exact ⟨⟨_,hm⟩,hneq,hEV⟩
    have heLower : -(1/8 : ℝ) ≤ groundEnergy (fiberHamiltonian g 0) := by
      have hL := (hVac 0 (by simp)).2.1
      have hBound := hnum.2.2.1
      linarith
    have heUpper : groundEnergy (fiberHamiltonian g 0) ≤ 0 := by
      simpa only [norm_zero,zero_pow (by decide : 2 ≠ 0)] using (hVac 0 (by simp)).1
    have hThreshold : (7/8 : ℝ) ≤ nonvacuumThreshold g := by
      have hL := hnum.2.1
      unfold nonvacuumThreshold
      linarith
    refine ⟨hnum,hAuxNum,hThreshold,heLower,heUpper,hVac,?_,?_⟩
    · obtain ⟨he,hg,hs,hCD0,hquad,hLower,hWeighted,hScalar⟩ := hW g hgW
      have hdom := sm01_comparison_dominance I K hI hK
      have hScalarNew := WE06FixedReference_mono CU CT CN _ _ _ CD _ he g hg hs hLower hCD0 hquad
        (hCUK.trans hdom.2.2.2.2.1) (hCTI.trans hdom.2.2.2.2.2.1)
        (hCNK.trans hdom.2.2.2.2.2.2) hScalar
      refine ⟨he,hg,hs,hCD0,hquad,hLower,?_,hWeighted,hScalarNew,?_,?_,?_⟩
      · intro q
        exact (thresholdDiagonalMultiplier_sub_one_bound _ he g hg hs CD hCD0 hquad q).trans
          (mul_le_mul_of_nonneg_right hCDCm (sq_nonneg g))
      · have hdom := sm01_comparison_dominance I K hI hK
        have hK0 : 0 ≤ K := zero_le_one.trans hK
        have hI0 : 0 ≤ I := zero_le_one.trans hI
        have hJC : K ≤ sm01CJ I K := by
          have hKI : K ≤ K*I := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hI hK0
          have hEta1 : 1 ≤ sm01CEta I K := hK.trans hdom.1
          exact hKI.trans (by simpa only [sm01CJ,mul_one] using
            mul_le_mul_of_nonneg_left hEta1 (mul_nonneg hK0 hI0))
        have hSmall0 := (hWeighted 0 (by simp)).1
        have hzero := hZero _ he g hg hs hLower CD hCD0 hquad hSmall0
        refine ⟨?_,?_,?_,?_,?_,?_⟩
        · intro P hP
          obtain ⟨_,_,_,_,_,_,_,hnorm,_⟩ := hWeighted P hP
          exact hnorm.trans (hCWK.trans hdom.1)
        · intro q
          exact (hJ _ he g hg hs hLower CD hCD0 hquad hSmall0 q).trans
            (mul_le_mul_of_nonneg_right (hCJK.trans hJC) (sq_nonneg _))
        · intro q
          exact (hzero.1 q).trans
            (mul_le_mul_of_nonneg_right (hCZK.trans hdom.2.1) (sq_nonneg _))
        · filter_upwards [hzero.2] with q hq
          exact hq.trans (mul_le_mul_of_nonneg_right (hCZK.trans hdom.2.1) (sq_nonneg _))
        · intro P hP
          exact (hDelta _ he g hg hs hLower CD hCD0 hquad hSmall0 P hP (hWeighted P hP).1).trans
            (mul_le_mul_of_nonneg_right (hCDeltaK.trans hdom.2.2.1) (norm_nonneg P))
        · intro P hP
          filter_upwards [hEta _ he g hg hs hLower CD hCD0 hquad hSmall0 P hP (hWeighted P hP).1] with q hq
          exact ⟨hq.1.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hCEK.trans hdom.2.2.1) (norm_nonneg P)) (omega_nonneg q)),
            hq.2.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hCEK.trans hdom.2.2.2.1) (omega_nonneg q))
              (add_nonneg (omega_nonneg q) (norm_nonneg P)))⟩
      · intro P hP
        have hK0 : 0 ≤ K := zero_le_one.trans hK
        have hKI : K ≤ K*I := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hI hK0
        have hK2 : K ≤ 2*K := by linarith
        exact ⟨(hKop _ he g hg hs P hP).trans (hCKopK.trans hKI),
          (hLop _ he g hg hs P hP).trans (hCLopK.trans hKI),
          (hChi _ he g hg hs P hP).trans (hCChiK.trans hK2)⟩
      · intro hg0
        have hanchor : auxiliarySelfEnergy _ 0 he g hg hs = groundEnergy (fiberHamiltonian g 0) := by
          have hz := hquad 0
          simp only [norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero] at hz
          exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))
        have hSat : thresholdScalarN _ he g hg hs CD hCD0 hquad 0 (by simp) = kernelConstant _ he g hg hs 0 := by
          simpa only [thresholdScalarN,Complex.ofReal_re] using congrArg Complex.re
            (se03_saturation _ he g hg hs CD hCD0 hquad hnum.1 (hVac 0 (by simp)).2.1
              hnum.2.2.2.1 hanchor (hScalar.1 0 (by simp)) hg0)
        exact sm01_actual_scalar_margin I K hI hK _ he g hg hs hLower CD hCD0 hquad
          hScalarNew (KE02FixedReference_mono KK K _ he g hg hs hKKK (hKernel _ he g hg hs)) hSat hCa
    · intro hg0
      exact hPos g hg0 hgPos

end Froehlich
