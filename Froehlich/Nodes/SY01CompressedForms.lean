import Froehlich.Nodes.SY01SectorMaps
import Froehlich.Nodes.SY01IndexedForms
import Froehlich.Nodes.GW06Compression

/-! Symmetry of the actual indexed compressed forms and their weak equations. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem highEnergyConjugation_involutive (P : GW.Space) (n : ℕ) :
    Function.Involutive (highEnergyConjugation P n) := by
  intro u
  apply Subtype.ext
  exact energyConjugation_involutive P (u : EnergySpace P)

def highEnergyReflectionInv (P : GW.Space) (n : ℕ) (w : HighEnergySpace (-P) n) : HighEnergySpace P n :=
  ⟨(energyReflection P).symm w, by
    apply (highEnergy_mem_iff P n _).mpr
    apply (energyReflection P).injective
    rw [energyReflection_highProjection]
    simp only [LinearIsometryEquiv.apply_symm_apply]
    exact (highEnergy_mem_iff (-P) n (w : EnergySpace (-P))).mp w.property⟩

theorem highEnergyReflection_apply_inverse (P : GW.Space) (n : ℕ) (w : HighEnergySpace (-P) n) :
    highEnergyReflection P n (highEnergyReflectionInv P n w) = w := by
  apply Subtype.ext
  exact (energyReflection P).apply_symm_apply (w : EnergySpace (-P))

theorem compressedShiftedForm_conjugation (g lam : ℝ) (P : GW.Space) (n : ℕ)
    (i : Option GW.Operators.PositiveCutoff) (w u : HighEnergySpace P n) :
    (compressedFiberFormData g P n i).form (highEnergyConjugation P n w) (highEnergyConjugation P n u) -
      (lam : ℂ)*⟪highEnergyEmbedding P n (highEnergyConjugation P n w),
        highEnergyEmbedding P n (highEnergyConjugation P n u)⟫_ℂ =
      (starRingEnd ℂ) ((compressedFiberFormData g P n i).form w u -
        (lam : ℂ)*⟪highEnergyEmbedding P n w,highEnergyEmbedding P n u⟫_ℂ) := by
  exact indexedShiftedFiberForm_conjugation g lam P i (w : EnergySpace P) (u : EnergySpace P)

theorem compressedShiftedForm_reflection (g lam : ℝ) (P : GW.Space) (n : ℕ)
    (i : Option GW.Operators.PositiveCutoff) (w u : HighEnergySpace P n) :
    (compressedFiberFormData g (-P) n i).form (highEnergyReflection P n w) (highEnergyReflection P n u) -
      (lam : ℂ)*⟪highEnergyEmbedding (-P) n (highEnergyReflection P n w),
        highEnergyEmbedding (-P) n (highEnergyReflection P n u)⟫_ℂ =
      (compressedFiberFormData g P n i).form w u -
        (lam : ℂ)*⟪highEnergyEmbedding P n w,highEnergyEmbedding P n u⟫_ℂ := by
  exact indexedShiftedFiberForm_reflection g lam P i (w : EnergySpace P) (u : EnergySpace P)

theorem compressedWeak_conjugation (g lam : ℝ) (P : GW.Space) (n : ℕ)
    (i : Option GW.Operators.PositiveCutoff) (F : ConjugateLoad (HighEnergySpace P n))
    (x : HighEnergySpace P n)
    (hx : ∀ w, (compressedFiberFormData g P n i).form w x -
      (lam : ℂ)*⟪highEnergyEmbedding P n w,highEnergyEmbedding P n x⟫_ℂ = F w) :
    ∀ w, (compressedFiberFormData g P n i).form w (highEnergyConjugation P n x) -
      (lam : ℂ)*⟪highEnergyEmbedding P n w,highEnergyEmbedding P n (highEnergyConjugation P n x)⟫_ℂ =
        (starRingEnd ℂ) (F (highEnergyConjugation P n w)) := by
  intro w
  have h := compressedShiftedForm_conjugation g lam P n i (highEnergyConjugation P n w) x
  rw [highEnergyConjugation_involutive P n w,hx] at h
  exact h

theorem compressedWeak_reflection (g lam : ℝ) (P : GW.Space) (n : ℕ)
    (i : Option GW.Operators.PositiveCutoff) (F : ConjugateLoad (HighEnergySpace P n))
    (x : HighEnergySpace P n)
    (hx : ∀ w, (compressedFiberFormData g P n i).form w x -
      (lam : ℂ)*⟪highEnergyEmbedding P n w,highEnergyEmbedding P n x⟫_ℂ = F w) :
    ∀ w : HighEnergySpace (-P) n,
      (compressedFiberFormData g (-P) n i).form w (highEnergyReflection P n x) -
        (lam : ℂ)*⟪highEnergyEmbedding (-P) n w,highEnergyEmbedding (-P) n (highEnergyReflection P n x)⟫_ℂ =
          F (highEnergyReflectionInv P n w) := by
  intro w
  have h := compressedShiftedForm_reflection g lam P n i (highEnergyReflectionInv P n w) x
  rw [highEnergyReflection_apply_inverse,hx] at h
  exact h

end Froehlich
