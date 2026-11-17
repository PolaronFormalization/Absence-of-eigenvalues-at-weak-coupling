import Froehlich.Nodes.SM01Numeric

set_option autoImplicit false
noncomputable section
namespace Froehlich

/-! SM01 finite absorption and literal comparison constants (source lines2493–2542).
Pure numerical witnesses only: no model estimates or final spectral premise. -/

theorem sm01_finite_absorption (sigma Cbase : ℝ) (hsigma : 0 < sigma) (hbase : 0 ≤ Cbase) :
    ∃ Cm : ℝ, Cbase ≤ Cm ∧ 0 ≤ Cm ∧ 1/(2*Real.sqrt (1+Cm)) ≤ sigma ∧
      ∀ sPre K I : ℝ, sm01AuxCutoff sPre Cm K I ≤ sigma := by
  let Cm := Cbase+(sigma⁻¹)^2+1
  have hCm : 0 ≤ Cm := by dsimp [Cm]; positivity
  have hbaseCm : Cbase ≤ Cm := by dsimp [Cm]; nlinarith [sq_nonneg sigma⁻¹]
  have harg : 0 < 1+Cm := by linarith
  have hr : 0 < Real.sqrt (1+Cm) := Real.sqrt_pos.mpr harg
  have hsqrt : sigma⁻¹ ≤ Real.sqrt (1+Cm) := by
    have hh := Real.sq_sqrt harg.le
    have hi : 0 < sigma⁻¹ := inv_pos.mpr hsigma
    dsimp [Cm] at hh
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsqrt hsigma.le
  rw [mul_inv_cancel₀ hsigma.ne'] at hmul
  have hsmall : 1/(2*Real.sqrt (1+Cm)) ≤ sigma := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hr)).mpr
    nlinarith
  refine ⟨Cm,hbaseCm,hCm,hsmall,?_⟩
  intro sPre K I
  exact ((min_le_right _ _).trans (min_le_left _ _)).trans hsmall

def sm01CEta (I K : ℝ) : ℝ := 16*K/3
def sm01CJ (I K : ℝ) : ℝ := K*I*sm01CEta I K
def sm01CZero (I K : ℝ) : ℝ := (4/3)*(K+sm01CJ I K)
def sm01CDelta (I K : ℝ) : ℝ := (8/3)*(K+2*K*I*sm01CZero I K)
def sm01CSharp (I K : ℝ) : ℝ := sm01CZero I K+sm01CDelta I K
def sm01CU (I K : ℝ) : ℝ := I*sm01CSharp I K
def sm01CT (I K : ℝ) : ℝ := 2*I
def sm01CN (I K : ℝ) : ℝ := K*I*(sm01CEta I K+sm01CDelta I K+sm01CZero I K)
def sm01CommonC (I K : ℝ) : ℝ := max 1 (max K (max (sm01CU I K) (max (sm01CT I K) (sm01CN I K))))
def sm01FinalCutoff (sAux I K : ℝ) : ℝ := min (sAux/2) (1/(4*sm01CommonC I K))

theorem sm01_comparison_dominance (I K : ℝ) (hI : 1 ≤ I) (hK : 1 ≤ K) :
    K ≤ sm01CEta I K ∧ K ≤ sm01CZero I K ∧ K ≤ sm01CDelta I K ∧
      K ≤ sm01CSharp I K ∧ K ≤ sm01CU I K ∧ I ≤ sm01CT I K ∧ K ≤ sm01CN I K := by
  have hI0 : 0 ≤ I := le_trans zero_le_one hI
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have he : K ≤ sm01CEta I K := by dsimp [sm01CEta]; linarith
  have he0 : 0 ≤ sm01CEta I K := hK0.trans he
  have hj0 : 0 ≤ sm01CJ I K := mul_nonneg (mul_nonneg hK0 hI0) he0
  have hz : K ≤ sm01CZero I K := by dsimp [sm01CZero]; linarith
  have hz0 : 0 ≤ sm01CZero I K := hK0.trans hz
  have hd : K ≤ sm01CDelta I K := by
    have hh : 0 ≤ 2*K*I*sm01CZero I K := by positivity
    dsimp [sm01CDelta]
    linarith
  have hd0 : 0 ≤ sm01CDelta I K := hK0.trans hd
  have hsharp : K ≤ sm01CSharp I K := by dsimp [sm01CSharp]; linarith
  have hsharp0 : 0 ≤ sm01CSharp I K := hK0.trans hsharp
  have hu : K ≤ sm01CU I K := hsharp.trans (by
    simpa only [sm01CU,one_mul] using mul_le_mul_of_nonneg_right hI hsharp0)
  have ht : I ≤ sm01CT I K := by dsimp [sm01CT]; linarith
  have hsum : 1 ≤ sm01CEta I K+sm01CDelta I K+sm01CZero I K := by linarith
  have hki : K ≤ K*I := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hI hK0
  have hn : K ≤ sm01CN I K := hki.trans (by
    simpa only [sm01CN,mul_one] using mul_le_mul_of_nonneg_left hsum (mul_nonneg hK0 hI0))
  exact ⟨he,hz,hd,hsharp,hu,ht,hn⟩

theorem sm01CommonC_dominance (I K : ℝ) :
    1 ≤ sm01CommonC I K ∧ K ≤ sm01CommonC I K ∧ sm01CU I K ≤ sm01CommonC I K ∧
      sm01CT I K ≤ sm01CommonC I K ∧ sm01CN I K ≤ sm01CommonC I K := by
  simp only [sm01CommonC]
  exact ⟨le_max_left _ _,(le_max_left _ _).trans (le_max_right _ _),
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))),
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))⟩

theorem sm01FinalCutoff_pos (sAux I K : ℝ) (hs : 0 < sAux) :
    0 < sm01FinalCutoff sAux I K := by
  have hC : 0 < sm01CommonC I K := lt_of_lt_of_le zero_lt_one (sm01CommonC_dominance I K).1
  unfold sm01FinalCutoff
  positivity

end Froehlich
