import GW.Operators.ResolventAlgebra

/-! DF01: spectra use the retained full-domain, two-sided inverse predicate. -/
noncomputable section
namespace Froehlich
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def complexResolventSet (A : H →ₗ.[ℂ] H) : Set ℂ :=
  {z | ∃ R : H →L[ℂ] H, GW.Operators.IsResolvent A z R}

def complexSpectrum (A : H →ₗ.[ℂ] H) : Set ℂ := (complexResolventSet A)ᶜ

def realResolventSet (A : H →ₗ.[ℂ] H) : Set ℝ :=
  {lam | ∃ R : H →L[ℂ] H, GW.Operators.IsResolvent A (lam : ℂ) R}

def realSpectrum (A : H →ₗ.[ℂ] H) : Set ℝ := (realResolventSet A)ᶜ

def groundEnergy (A : H →ₗ.[ℂ] H) : ℝ := sInf (realSpectrum A)

def HasEigenvector (A : H →ₗ.[ℂ] H) (lam : ℝ) : Prop :=
  ∃ u : A.domain, (u : H) ≠ 0 ∧ A u = (lam : ℂ) • (u : H)

@[simp] theorem realSpectrum_eq_preimage (A : H →ₗ.[ℂ] H) :
    realSpectrum A = Complex.ofReal ⁻¹' complexSpectrum A := rfl

@[simp] theorem realResolventSet_eq_preimage (A : H →ₗ.[ℂ] H) :
    realResolventSet A = Complex.ofReal ⁻¹' complexResolventSet A := rfl

/-- A genuine operator-domain eigenvector obstructs a bounded two-sided inverse. -/
theorem HasEigenvector.mem_realSpectrum {A : H →ₗ.[ℂ] H} {lam : ℝ}
    (h : HasEigenvector A lam) : lam ∈ realSpectrum A := by
  rintro ⟨R, hR⟩
  obtain ⟨u, hne, hu⟩ := h
  have hz : GW.Operators.complexShift A (lam : ℂ) u = 0 := by
    change A u - (lam : ℂ) • (u : H) = 0
    rw [hu, sub_self]
  have hi := hR.right_inv u
  rw [hz, map_zero] at hi
  exact hne hi.symm

/-- FA05's order argument needs neither a spectral theorem nor nonreal analysis. -/
theorem groundEnergy_eq_of_bottom {A : H →ₗ.[ℂ] H} {e : ℝ}
    (he : e ∈ realSpectrum A)
    (hl : ∀ lam < e, lam ∈ realResolventSet A) : groundEnergy A = e := by
  have hb : ∀ x ∈ realSpectrum A, e ≤ x := by
    intro x hx
    by_contra h
    exact hx (hl x (lt_of_not_ge h))
  apply le_antisymm
  · exact csInf_le ⟨e, hb⟩ he
  · exact le_csInf ⟨e, he⟩ hb
end Froehlich
