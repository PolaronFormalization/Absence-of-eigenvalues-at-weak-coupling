import Froehlich.Nodes.SP01EnergyResolvent
import Froehlich.Nodes.SP01Nonnegative

/-! Full real-spectrum exhaustion and identification of its infimum,
conditioned only on an actual vacuum Schur root. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem vacuumRoot_spectrum_below (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (e : Set.Iio (nonvacuumThreshold g)) (hroot : vacuumSchurFunction g P hg e = 0) :
    realSpectrum (fiberHamiltonian g P) ∩ Set.Iio (nonvacuumThreshold g) = {(e : ℝ)} := by
  ext lam
  constructor
  · rintro ⟨hs,hl⟩
    by_cases hF : vacuumSchurFunction g P hg ⟨lam,hl⟩ = 0
    · have he := vacuumSchurFunction_root_unique g P hg ⟨lam,hl⟩ e hF hroot
      exact Set.mem_singleton_iff.mpr (congrArg Subtype.val he)
    · exact False.elim (hs (vacuumSchurFunction_ne_zero_mem_resolvent g P hg ⟨lam,hl⟩ hF))
  · intro h
    have he : lam = (e : ℝ) := Set.mem_singleton_iff.mp h
    subst lam
    exact ⟨(vacuumSchurVector_eigenvector g P hg e hroot).mem_realSpectrum,e.property⟩

theorem vacuumRoot_groundEnergy (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (e : Set.Iio (nonvacuumThreshold g)) (hroot : vacuumSchurFunction g P hg e = 0) :
    groundEnergy (fiberHamiltonian g P) = (e : ℝ) := by
  apply groundEnergy_eq_of_bottom (vacuumSchurVector_eigenvector g P hg e hroot).mem_realSpectrum
  intro lam hl
  have hlam : lam < nonvacuumThreshold g := hl.trans e.property
  apply vacuumSchurFunction_ne_zero_mem_resolvent g P hg ⟨lam,hlam⟩
  intro hF
  have he := vacuumSchurFunction_root_unique g P hg ⟨lam,hlam⟩ e hF hroot
  have he' := congrArg Subtype.val he
  exact (ne_of_lt hl) he'

theorem vacuumRoot_energy_lower (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (e : Set.Iio (nonvacuumThreshold g)) (hroot : vacuumSchurFunction g P hg e = 0) :
    -(sectorEnergyConstant*|g|^2) ≤ (e : ℝ) := by
  let u := vacuumSchurVectorEnergy g P hg e
  have hn : 0 < ‖energyEmbedding P u‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (vacuumSchurVector_embedding_ne_zero g P hg e))
  have hb := fiberForm_global_lower g P u hg
  have he := vacuumSchurVector_weak_equation g P hg e hroot u
  have hi : (⟪energyEmbedding P u,energyEmbedding P u⟫_ℂ).re = ‖energyEmbedding P u‖^2 := by
    simpa only [RCLike.re_eq_complex_re] using
      (norm_sq_eq_re_inner (𝕜 := ℂ) (energyEmbedding P u)).symm
  have hr := congrArg Complex.re he
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hr
  rw [hi] at hr
  change ((fiberFormData g P none).form u u).re = (e : ℝ)*‖energyEmbedding P u‖^2 at hr
  nlinarith

end Froehlich
