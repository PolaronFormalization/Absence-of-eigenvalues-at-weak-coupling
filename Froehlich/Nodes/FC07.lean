import Froehlich.Nodes.FC03
import Froehlich.Nodes.FC09
import GW.Fock.FockPullthrough

/-! FC07: finite-sector field commutations, using the retained maximal CCR. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

theorem fockField_ext_of_contractions
    (u v : Lp GW.Fock.Carrier 2 (volume : Measure GW.Space))
    (h : ∀ f : GW.OnePhonon, GW.Fock.contraction volume f u = GW.Fock.contraction volume f v) : u = v := by
  apply sub_eq_zero.mp
  apply residual_zero_of_dense_scalar_tests volume (u-v) ⊤
  · simpa using (dense_univ : Dense (Set.univ : Set GW.Fock.Carrier))
  · intro w _ f
    rw [residual_test_eq_contraction_inner, map_sub, h f, sub_self, inner_zero_right]

def finiteNumberLift : GW.Fock.finiteSectorDomain GW.Fock.Sector →ₗ[ℂ] NumberFormSpace :=
  numberFormGraph.product.comp (Submodule.inclusion
    (GW.Fock.finiteSectorDomain_le GW.Fock.Sector (fun n => ((n : ℝ)+1)^(1/2 : ℝ))))

theorem finiteNumberLift_embedding (u : GW.Fock.finiteSectorDomain GW.Fock.Sector) :
    numberFormEmbedding (finiteNumberLift u) = (u : GW.Fock.Carrier) :=
  numberFormGraph.embedding_product _

def finiteRootSector (M : ℕ) (n : ℕ) : GW.Fock.Sector n →L[ℂ] GW.Fock.Sector n :=
  if n ≤ M then (Real.sqrt ((n : ℝ)+1) : ℂ) • ContinuousLinearMap.id ℂ (GW.Fock.Sector n) else 0

theorem finiteRootSector_norm (M n : ℕ) : ‖finiteRootSector M n‖ ≤ Real.sqrt ((M : ℝ)+1) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  unfold finiteRootSector
  by_cases hn : n ≤ M
  · rw [if_pos hn]
    change ‖(Real.sqrt ((n : ℝ)+1) : ℂ) • u‖ ≤ _
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.sqrt_le_sqrt
    have hcast : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hn
    exact add_le_add hcast (le_refl (1 : ℝ))
  · simp only [if_neg hn, ContinuousLinearMap.zero_apply, norm_zero]
    positivity

/-- Bounded lift of the actual particle cutoff to number coordinates. -/
def finiteRootLift (M : ℕ) : GW.Fock.Carrier →L[ℂ] NumberFormSpace :=
  GW.Spaces.diagonalMap (finiteRootSector M) (Real.sqrt_nonneg _) (finiteRootSector_norm M)

theorem finiteRootLift_embedding (M : ℕ) (u : GW.Fock.Carrier) :
    numberFormEmbedding (finiteRootLift M u) = lowSectorProjection M u := by
  apply lp.ext
  funext n
  rw [numberFormEmbedding_sqrt_apply]
  change (((Real.sqrt ((n : ℝ)+1))⁻¹ : ℝ) : ℂ) • finiteRootSector M n (u n) = _
  change (((Real.sqrt ((n : ℝ)+1))⁻¹ : ℝ) : ℂ) • finiteRootSector M n (u n) =
    GW.Fock.cutoff GW.Fock.Sector M u n
  rw [GW.Fock.cutoff_apply]
  unfold finiteRootSector
  by_cases hn : n ≤ M
  · rw [if_pos hn, if_pos hn]
    change (((Real.sqrt ((n : ℝ)+1))⁻¹ : ℝ) : ℂ) •
      ((Real.sqrt ((n : ℝ)+1) : ℂ) • u n) = u n
    rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by positivity))),
      Complex.ofReal_one, one_smul]
  · rw [if_neg hn, if_neg hn]
    simp only [ContinuousLinearMap.zero_apply, smul_zero]

def finiteCreationMap (M : ℕ) (f : GW.OnePhonon) : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  (creationRestriction f).comp (finiteRootLift M)

def finiteAnnihilationMap (M : ℕ) (f : GW.OnePhonon) : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  (annihilationRestriction f).comp (finiteRootLift M)

end Froehlich
