import Froehlich.Nodes.GW03
import Froehlich.Nodes.GW04Product
import GW.Fock.FockFieldDefinition

/-! GW04: continuous restrictions of the existing maximal smeared operators.
Only the complete input graph carrier is used for continuity; maximal domains stay unchanged. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace Froehlich

def numberRootLinear : NumberFormSpace →ₗ[ℂ]
    (GW.Fock.numberPower GW.Fock.Sector (1/2)).domain where
  toFun := numberFormRootInput
  map_add' x y := Subtype.ext (numberFormEmbedding.map_add x y)
  map_smul' c x := Subtype.ext (numberFormEmbedding.map_smul c x)

def annihilationRootInclusion (f : GW.OnePhonon) :
    (GW.Fock.numberPower GW.Fock.Sector (1/2)).domain →ₗ[ℂ] (GW.Fock.ordinaryAnnihilation f).domain :=
  Submodule.inclusion (fun u hu => (GW.Fock.ordinaryAnnihilationRootInput f ⟨u,hu⟩).property)

def creationRootInclusion (f : GW.OnePhonon) :
    (GW.Fock.numberPower GW.Fock.Sector (1/2)).domain →ₗ[ℂ] (GW.Fock.ordinaryCreation f).domain :=
  Submodule.inclusion (fun u hu => (GW.Fock.ordinaryCreationRootInput f ⟨u,hu⟩).property)

def annihilationRestrictionLinear (f : GW.OnePhonon) : NumberFormSpace →ₗ[ℂ] GW.Fock.Carrier :=
  (GW.Fock.ordinaryAnnihilation f).toFun.comp ((annihilationRootInclusion f).comp numberRootLinear)

def creationRestrictionLinear (f : GW.OnePhonon) : NumberFormSpace →ₗ[ℂ] GW.Fock.Carrier :=
  (GW.Fock.ordinaryCreation f).toFun.comp ((creationRootInclusion f).comp numberRootLinear)

theorem annihilationRestrictionLinear_apply (f : GW.OnePhonon) (x : NumberFormSpace) :
    annihilationRestrictionLinear f x = GW.Fock.ordinaryAnnihilation f
      (GW.Fock.ordinaryAnnihilationRootInput f (numberFormRootInput x)) := rfl

theorem creationRestrictionLinear_apply (f : GW.OnePhonon) (x : NumberFormSpace) :
    creationRestrictionLinear f x = GW.Fock.ordinaryCreation f
      (GW.Fock.ordinaryCreationRootInput f (numberFormRootInput x)) := rfl

theorem ordinaryKernel_norm (f : GW.OnePhonon) : ‖GW.Fock.ordinaryKernel f‖ = ‖f‖ :=
  ContinuousLinearMap.norm_toSpanSingleton (𝕜 := ℂ) f

theorem annihilationRestriction_sharp_bound (f : GW.OnePhonon) (x : NumberFormSpace) :
    ‖annihilationRestrictionLinear f x‖ ≤ ‖f‖ *
      ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput x)‖ := by
  have h := GW.Fock.annihilation_root_norm GW.Fock.ordinarySectorKernel
    (GW.Fock.ordinaryKernel f) (numberFormRootInput x)
  change ‖annihilationRestrictionLinear f x‖ ≤ ‖GW.Fock.ordinaryKernel f‖ *
    ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput x)‖ at h
  rw [ordinaryKernel_norm] at h
  exact h

theorem creationRestriction_sharp_bound (f : GW.OnePhonon) (x : NumberFormSpace) :
    ‖creationRestrictionLinear f x‖ ≤ ‖f‖ *
      ‖GW.Fock.shiftedNumberPower GW.Fock.Sector (1/2)
        (GW.Fock.shiftedNumberInput GW.Fock.Sector (1/2) (by positivity) (numberFormRootInput x))‖ := by
  have h := GW.Fock.creation_root_norm GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f)
    (GW.Fock.shiftedNumberInput GW.Fock.Sector (1/2) (by positivity) (numberFormRootInput x))
  change ‖creationRestrictionLinear f x‖ ≤ ‖GW.Fock.ordinaryKernel f‖ *
    ‖GW.Fock.shiftedNumberPower GW.Fock.Sector (1/2)
      (GW.Fock.shiftedNumberInput GW.Fock.Sector (1/2) (by positivity) (numberFormRootInput x))‖ at h
  rw [ordinaryKernel_norm] at h
  exact h

theorem shiftedNumberRoot_numberForm (x : NumberFormSpace) :
    GW.Fock.shiftedNumberPower GW.Fock.Sector (1/2)
      (GW.Fock.shiftedNumberInput GW.Fock.Sector (1/2) (by positivity) (numberFormRootInput x)) =
        (show GW.Fock.Carrier from x) :=
  numberFormGraph.product_embedding x

theorem numberFormRoot_norm_le (x : NumberFormSpace) :
    ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput x)‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h := numberForm_norm_identity x
  nlinarith [sq_nonneg ‖numberFormEmbedding x‖]

theorem annihilationRestriction_bound (f : GW.OnePhonon) (x : NumberFormSpace) :
    ‖annihilationRestrictionLinear f x‖ ≤ ‖f‖ * ‖x‖ :=
  (annihilationRestriction_sharp_bound f x).trans
    (mul_le_mul_of_nonneg_left (numberFormRoot_norm_le x) (norm_nonneg f))

theorem creationRestriction_bound (f : GW.OnePhonon) (x : NumberFormSpace) :
    ‖creationRestrictionLinear f x‖ ≤ ‖f‖ * ‖x‖ := by
  have h := creationRestriction_sharp_bound f x
  rw [shiftedNumberRoot_numberForm] at h
  exact h

def annihilationRestriction (f : GW.OnePhonon) : NumberFormSpace →L[ℂ] GW.Fock.Carrier :=
  (annihilationRestrictionLinear f).mkContinuous ‖f‖ (annihilationRestriction_bound f)

def creationRestriction (f : GW.OnePhonon) : NumberFormSpace →L[ℂ] GW.Fock.Carrier :=
  (creationRestrictionLinear f).mkContinuous ‖f‖ (creationRestriction_bound f)

theorem annihilationRestriction_opNorm (f : GW.OnePhonon) : ‖annihilationRestriction f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro x
  change ‖annihilationRestrictionLinear f x‖ ≤ ‖f‖ * ‖x‖
  exact annihilationRestriction_bound f x

theorem creationRestriction_opNorm (f : GW.OnePhonon) : ‖creationRestriction f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro x
  change ‖creationRestrictionLinear f x‖ ≤ ‖f‖ * ‖x‖
  exact creationRestriction_bound f x

theorem annihilationRestriction_apply (f : GW.OnePhonon) (x : NumberFormSpace) :
    annihilationRestriction f x = GW.Fock.ordinaryAnnihilation f
      (GW.Fock.ordinaryAnnihilationRootInput f (numberFormRootInput x)) := rfl

theorem creationRestriction_apply (f : GW.OnePhonon) (x : NumberFormSpace) :
    creationRestriction f x = GW.Fock.ordinaryCreation f
      (GW.Fock.ordinaryCreationRootInput f (numberFormRootInput x)) := rfl

def fieldRestriction (f : GW.OnePhonon) : NumberFormSpace →L[ℂ] GW.Fock.Carrier :=
  annihilationRestriction f + creationRestriction f

theorem fieldRestriction_eq_ordinaryField (f : GW.OnePhonon) (x : NumberFormSpace) :
    fieldRestriction f x = GW.Fock.ordinaryField f (numberFormRootInput x) := by
  change GW.Fock.ordinaryAnnihilation f (GW.Fock.ordinaryAnnihilationRootInput f (numberFormRootInput x)) +
    GW.Fock.ordinaryCreation f (GW.Fock.ordinaryCreationRootInput f (numberFormRootInput x)) = _
  exact (GW.Fock.ordinaryField_action f (numberFormRootInput x)).symm

theorem ordinaryKernel_adjoint (f : GW.OnePhonon) :
    (GW.Fock.ordinaryKernel f).adjoint = GW.Fock.contraction volume f := by
  ext g
  change (ContinuousLinearMap.toSpanSingleton ℂ f).adjoint g = _
  rw [ContinuousLinearMap.adjoint_toSpanSingleton]
  exact (contraction_scalar volume f g).symm

theorem kernelAnnihilationRaw_contraction (f : GW.OnePhonon) (n : ℕ)
    (v : GW.Fock.AmbientSector (n+1)) :
    GW.Fock.kernelAnnihilationRaw (GW.Fock.ordinaryKernel f) n v =
      GW.Fock.contraction volume f (ambientCurrying n v) := by
  change GW.Fock.amplify (GW.Fock.sectorMeasure n) (GW.Fock.ordinaryKernel f).adjoint
    ((GW.Fock.productUnitary (E := ℂ) (GW.Fock.sectorMeasure n) volume).symm
      (GW.Fock.swapProduct volume (GW.Fock.sectorMeasure n) (GW.Fock.splitUnitary n 0 v))) =
    GW.Fock.contraction volume f
      ((GW.Fock.productUnitary (E := ℂ) volume (GW.Fock.sectorMeasure n)).symm (GW.Fock.splitUnitary n 0 v))
  rw [ordinaryKernel_adjoint, ← GW.Fock.spectatorContraction_identification]
  exact (contraction_inverseProduct_swap volume (GW.Fock.sectorMeasure n) f
    (GW.Fock.splitUnitary n 0 v)).symm

theorem ordinarySectorAnnihilation_contraction (f : GW.OnePhonon) (n : ℕ)
    (u : GW.Fock.Sector (n+1)) :
    GW.Fock.sectorAnnihilation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n u =
      GW.Fock.contraction volume f
        ((Real.sqrt (n+1 : ℕ) : ℂ) • sectorCurrying n u) := by
  let J : GW.Fock.Sector n →ₗᵢ[ℂ] GW.Fock.AmbientSector n :=
    (GW.Fock.kernelFixedInclusion n).comp (GW.Fock.ordinarySectorKernel n).toLinearIsometry
  apply J.injective
  have hJ : GW.Fock.amplify volume J.toContinuousLinearMap (sectorCurrying n u) =
      rawSectorCurrying n u := by
    apply Lp.ext
    filter_upwards [GW.Fock.amplify_ae volume J.toContinuousLinearMap (sectorCurrying n u),
      sectorCurrying_kernelRepresentative_ae n u] with k hk hr
    rw [hk]
    exact hr
  have hleft : J (GW.Fock.sectorAnnihilation GW.Fock.ordinarySectorKernel
      (GW.Fock.ordinaryKernel f) n u) =
      (Real.sqrt (n+1 : ℕ) : ℂ) • GW.Fock.contraction volume f (rawSectorCurrying n u) := by
    change GW.Fock.kernelFixedInclusion n (GW.Fock.ordinarySectorKernel n
      ((GW.Fock.ordinarySectorKernel n).symm (GW.Fock.kernelAnnihilation
        (GW.Fock.ordinaryKernel f) n (GW.Fock.ordinarySectorKernel (n+1) u)))) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
    change (GW.Fock.kernelAnnihilation (GW.Fock.ordinaryKernel f) n
      (GW.Fock.ordinarySectorKernel (n+1) u) : GW.Fock.KernelSector ℂ n) = _
    rw [GW.Fock.kernelAnnihilation_value]
    have hv : (GW.Fock.ordinarySectorKernel (n+1) u : GW.Fock.KernelSector ℂ (n+1)) =
        GW.Fock.sectorInclusion n u := rfl
    rw [hv, kernelAnnihilationRaw_contraction]
    rfl
  have hright : J (GW.Fock.contraction volume f
      ((Real.sqrt (n+1 : ℕ) : ℂ) • sectorCurrying n u)) =
      (Real.sqrt (n+1 : ℕ) : ℂ) • GW.Fock.contraction volume f (rawSectorCurrying n u) := by
    change J.toContinuousLinearMap (GW.Fock.contraction volume f
      ((Real.sqrt (n+1 : ℕ) : ℂ) • sectorCurrying n u)) = _
    rw [contraction_natural, map_smul, hJ, map_smul]
  exact hleft.trans hright.symm

/-- Actual maximal annihilation on the physical root-number input equals the retained
Bochner contraction of the new momentum-indexed field. -/
theorem annihilationRestriction_eq_contraction (f : GW.OnePhonon) (x : NumberFormSpace) :
    annihilationRestriction f x = GW.Fock.contraction volume f (annihilationField x) := by
  apply lp.ext
  funext n
  rw [annihilationRestriction_apply, GW.Fock.ordinaryAnnihilation_apply]
  change GW.Fock.sectorAnnihilation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n
    (numberFormEmbedding x (n+1)) = (GW.Fock.contraction volume f (annihilationField x)) n
  have hn := contraction_natural volume (lp.evalCLM ℂ GW.Fock.Sector 2 n) f (annihilationField x)
  have hc : GW.Fock.amplify volume (lp.evalCLM ℂ GW.Fock.Sector 2 n) (annihilationField x) =
      annihilationSector n x := annihilationField_component x n
  rw [hc] at hn
  calc
    _ = GW.Fock.contraction volume f (annihilationSector n x) :=
      ordinarySectorAnnihilation_contraction f n (numberFormEmbedding x (n+1))
    _ = _ := hn.symm

theorem annihilationRestriction_integrable (f : GW.OnePhonon) (x : NumberFormSpace) :
    Integrable (fun k => (starRingEnd ℂ) (f k) • annihilationField x k) volume :=
  GW.Fock.contraction_integrable volume f (annihilationField x)

theorem annihilationRestriction_integral (f : GW.OnePhonon) (x : NumberFormSpace) :
    annihilationRestriction f x = ∫ k, (starRingEnd ℂ) (f k) • annihilationField x k := by
  rw [annihilationRestriction_eq_contraction]
  rfl

end Froehlich
