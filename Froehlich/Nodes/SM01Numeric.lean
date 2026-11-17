import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace Froehlich

/-! Numeric part of SM01, Froehlich-v5.tex lines2478–2507.
The six preliminary entries and four auxiliary entries are literal source
formulas. This generic arithmetic helper asserts no model/source-unit acceptance. -/

def sm01PreCutoff (CE C1 C2 CR CD : ℝ) : ℝ :=
  min (1/4) (min (1/(8*(1+C1))) (min (1/Real.sqrt (8*(1+CE)))
    (min (1/Real.sqrt (8*(1+C2))) (min (1/(2*(1+CR))) (1/Real.sqrt (2*(1+CD)))))))

def sm01AuxCutoff (sPre Cm K I : ℝ) : ℝ :=
  min (sPre/2) (min (1/(2*Real.sqrt (1+Cm)))
    (min (1/Real.sqrt (2*(1+(Cm+K*I)))) (Real.sqrt (3/(8*(1+K*I))))))

private theorem sm01_linear_guard (A B s : ℝ) (hA : 0 ≤ A) (hB : 0 < B)
    (hs : 0 ≤ s) (h : s ≤ 1/(B*(1+A))) : A*s ≤ 1/B := by
  have hden : 0 < B*(1+A) := mul_pos hB (by linarith)
  have hh := (le_div_iff₀ hden).mp h
  apply (le_div_iff₀ hB).mpr
  nlinarith [mul_nonneg hB.le hs]

private theorem sm01_square_guard (A B s : ℝ) (hA : 0 ≤ A) (hB : 0 < B)
    (hs : 0 ≤ s) (h : s ≤ 1/Real.sqrt (B*(1+A))) : A*s^2 ≤ 1/B := by
  have hden : 0 < B*(1+A) := mul_pos hB (by linarith)
  have hr : 0 < Real.sqrt (B*(1+A)) := Real.sqrt_pos.mpr hden
  have hh := (le_div_iff₀ hr).mp h
  have hsq : (s*Real.sqrt (B*(1+A)))^2 ≤ (1 : ℝ)^2 :=
    (sq_le_sq₀ (mul_nonneg hs hr.le) zero_le_one).mpr hh
  rw [mul_pow,Real.sq_sqrt hden.le] at hsq
  apply (le_div_iff₀ hB).mpr
  nlinarith [mul_nonneg hB.le (sq_nonneg s)]

theorem sm01PreCutoff_pos (CE C1 C2 CR CD : ℝ)
    (hCE : 0 ≤ CE) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hCR : 0 ≤ CR) (hCD : 0 ≤ CD) :
    0 < sm01PreCutoff CE C1 C2 CR CD := by
  unfold sm01PreCutoff
  positivity

theorem sm01PreCutoff_guards (CE C1 C2 CR CD s : ℝ)
    (hCE : 0 ≤ CE) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hCR : 0 ≤ CR) (hCD : 0 ≤ CD)
    (hs : 0 ≤ s) (hpre : s ≤ sm01PreCutoff CE C1 C2 CR CD) :
    s ≤ 1/4 ∧ C1*s ≤ 1/8 ∧ CE*s^2 ≤ 1/8 ∧ C2*s^2 ≤ 1/8 ∧
      CR*s ≤ 1/2 ∧ CD*s^2 ≤ 1/2 := by
  have h := hpre
  simp only [sm01PreCutoff,le_min_iff] at h
  exact ⟨h.1,sm01_linear_guard C1 8 s hC1 (by norm_num) hs h.2.1,
    sm01_square_guard CE 8 s hCE (by norm_num) hs h.2.2.1,
    sm01_square_guard C2 8 s hC2 (by norm_num) hs h.2.2.2.1,
    sm01_linear_guard CR 2 s hCR (by norm_num) hs h.2.2.2.2.1,
    sm01_square_guard CD 2 s hCD (by norm_num) hs h.2.2.2.2.2⟩

theorem sm01AuxCutoff_pos (sPre Cm K I : ℝ) (hPre : 0 < sPre)
    (hCm : 0 ≤ Cm) (hK : 0 ≤ K) (hI : 0 ≤ I) :
    0 < sm01AuxCutoff sPre Cm K I := by
  unfold sm01AuxCutoff
  positivity

theorem sm01AuxCutoff_guards (sPre Cm K I s : ℝ)
    (hCm : 0 ≤ Cm) (hK : 0 ≤ K) (hI : 0 ≤ I)
    (hs : 0 ≤ s) (haux : s ≤ sm01AuxCutoff sPre Cm K I) :
    s ≤ sPre/2 ∧ Cm*s^2 ≤ 1/4 ∧ (Cm+K*I)*s^2 ≤ 1/2 ∧
      (4/3 : ℝ)*s^2*K*I ≤ 1/2 := by
  have h := haux
  simp only [sm01AuxCutoff,le_min_iff] at h
  have hCm1 : 0 < 1+Cm := by linarith
  have hrCm : 0 < Real.sqrt (1+Cm) := Real.sqrt_pos.mpr hCm1
  have hmul := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hrCm)).mp h.2.1
  have hsq : (s*(2*Real.sqrt (1+Cm)))^2 ≤ (1 : ℝ)^2 :=
    (sq_le_sq₀ (mul_nonneg hs (mul_pos (by norm_num) hrCm).le) zero_le_one).mpr hmul
  simp only [mul_pow,Real.sq_sqrt hCm1.le] at hsq
  have hCmGuard : Cm*s^2 ≤ 1/4 := by nlinarith [sq_nonneg s]
  have hCB := sm01_square_guard (Cm+K*I) 2 s (add_nonneg hCm (mul_nonneg hK hI))
    (by norm_num) hs h.2.2.1
  have hKI : 0 ≤ K*I := mul_nonneg hK hI
  have hden : 0 < 8*(1+K*I) := by positivity
  have harg : 0 ≤ 3/(8*(1+K*I)) := by positivity
  have hroot := (sq_le_sq₀ hs (Real.sqrt_nonneg _)).mpr h.2.2.2
  rw [Real.sq_sqrt harg] at hroot
  have hbound := (le_div_iff₀ hden).mp hroot
  have hNeumann : (4/3 : ℝ)*s^2*K*I ≤ 1/2 := by nlinarith [sq_nonneg s]
  exact ⟨h.1,hCmGuard,hCB,hNeumann⟩

/-- The entire one-phonon window has the source's closed lower denominator margin. -/
theorem sm01_window_denominator (e p eps : ℝ) (he : -(1/8 : ℝ) ≤ e)
    (hp0 : 0 ≤ p) (hp : p ≤ 1/4) (heps : eps ≤ 1/8) :
    (11/16 : ℝ) ≤ 1+e-p^2-eps := by
  nlinarith

end Froehlich
