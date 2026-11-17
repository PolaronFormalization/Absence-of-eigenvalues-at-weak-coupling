import Froehlich.Nodes.FC02
import Froehlich.Nodes.FC01Fields
import GW.Fock.FockCcr

/-! FC06: source-normalized sector operations and their actual maximal
operators, restricted continuously to the same number graph carrier. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem smeared_sector_pairing (f : GW.OnePhonon) (n : ℕ)
    (w : GW.Fock.Sector n) (u : GW.Fock.Sector (n+1)) :
    ⟪GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n w,u⟫_ℂ =
      ⟪w,GW.Fock.sectorAnnihilation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n u⟫_ℂ :=
  GW.Fock.sectorCreation_pairing GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n w u

theorem smeared_adjoint_pairing (f : GW.OnePhonon) (w u : NumberFormSpace) :
    ⟪creationRestriction f w,numberFormEmbedding u⟫_ℂ =
      ⟪numberFormEmbedding w,annihilationRestriction f u⟫_ℂ := by
  exact GW.Fock.ccr_graph_pair_creation f (numberFormEmbedding w) (creationRestriction f w)
    (numberFormEmbedding u) (annihilationRestriction f u)
    ((GW.Fock.ordinaryCreation f).mem_graph
      (GW.Fock.ordinaryCreationRootInput f (numberFormRootInput w)))
    ((GW.Fock.ordinaryAnnihilation f).mem_graph
      (GW.Fock.ordinaryAnnihilationRootInput f (numberFormRootInput u)))

theorem smeared_creation_norm_identity (f : GW.OnePhonon) (u : NumberFormSpace) :
    ‖creationRestriction f u‖ ^ 2 = ‖annihilationRestriction f u‖ ^ 2 +
      ‖f‖ ^ 2 * ‖numberFormEmbedding u‖ ^ 2 := by
  exact GW.Fock.ordinaryCreation_norm_identity f
    (GW.Fock.ordinaryAnnihilationRootInput f (numberFormRootInput u))
    (GW.Fock.ordinaryCreationRootInput f (numberFormRootInput u)).property

theorem smeared_annihilation_norm_sq (f : GW.OnePhonon) (u : NumberFormSpace) :
    ‖annihilationRestriction f u‖ ^ 2 ≤
      ‖f‖ ^ 2 * (∑' m : ℕ, (m : ℝ) * ‖numberFormEmbedding u m‖ ^ 2) := by
  have h := annihilationRestriction_sharp_bound f u
  change ‖annihilationRestriction f u‖ ≤ _ at h
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  rw [mul_pow, numberFormRoot_norm] at hs
  exact hs

theorem smeared_creation_graph_bound (f : GW.OnePhonon) :
    ‖creationRestriction f‖ ≤ ‖f‖ := creationRestriction_opNorm f

theorem smeared_annihilation_graph_bound (f : GW.OnePhonon) :
    ‖annihilationRestriction f‖ ≤ ‖f‖ := annihilationRestriction_opNorm f

/-- This exact sector formula retains the source factor sqrt(n+1), including
the scalar vacuum output n=0. -/
theorem smeared_annihilation_sector_contraction (f : GW.OnePhonon) (n : ℕ)
    (u : GW.Fock.Sector (n+1)) :
    GW.Fock.sectorAnnihilation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n u =
      GW.Fock.contraction volume f ((Real.sqrt (n+1 : ℕ) : ℂ) • sectorCurrying n u) :=
  ordinarySectorAnnihilation_contraction f n u

theorem smeared_annihilation_integrable (f : GW.OnePhonon) (u : NumberFormSpace) :
    Integrable (fun k => (starRingEnd ℂ) (f k) • annihilationField u k) volume :=
  annihilationRestriction_integrable f u

theorem smeared_annihilation_integral (f : GW.OnePhonon) (u : NumberFormSpace) :
    annihilationRestriction f u = ∫ k, (starRingEnd ℂ) (f k) • annihilationField u k :=
  annihilationRestriction_integral f u

theorem ambient_contraction_sections (f : GW.OnePhonon) (n : ℕ)
    (u : GW.Fock.AmbientSector (n+1)) :
    ∀ᵐ K ∂GW.Fock.sectorMeasure n,
      Integrable (fun k : GW.Space => (starRingEnd ℂ) (f k) *
        u ((GW.Fock.splitCoordinates n 0).symm (k,K))) volume ∧
      GW.Fock.contraction volume f (ambientCurrying n u) K =
        ∫ k : GW.Space, (starRingEnd ℂ) (f k) *
          u ((GW.Fock.splitCoordinates n 0).symm (k,K)) := by
  let v := GW.Fock.splitUnitary n 0 u
  let w := GW.Fock.swapProduct volume (GW.Fock.sectorMeasure n) v
  have hw : w =ᵐ[(GW.Fock.sectorMeasure n).prod (volume : Measure GW.Space)]
      (fun p => u ((GW.Fock.splitCoordinates n 0).symm (p.2,p.1))) :=
    (GW.Fock.swapProduct_ae volume (GW.Fock.sectorMeasure n) v).trans
      ((Measure.measurePreserving_swap (μ := GW.Fock.sectorMeasure n)
        (ν := (volume : Measure GW.Space))).quasiMeasurePreserving.ae
          (GW.Fock.splitUnitary_ae n 0 u))
  have hsections := Measure.ae_ae_of_ae_prod hw
  have he : GW.Fock.contraction volume f (ambientCurrying n u) =
      GW.Fock.spectatorContraction (GW.Fock.sectorMeasure n) volume f w :=
    contraction_inverseProduct_swap volume (GW.Fock.sectorMeasure n) f v
  rw [he]
  filter_upwards [hsections, GW.Fock.product_slice_memLp (GW.Fock.sectorMeasure n) volume w,
    GW.Fock.spectatorContractionClass_ae (GW.Fock.sectorMeasure n) volume f w] with K hK hmem hvalue
  have hi := GW.Fock.slice_contraction_integrable volume f hmem
  have hprod : (fun k : GW.Space => (starRingEnd ℂ) (f k) • w (K,k)) =ᵐ[volume]
      (fun k => (starRingEnd ℂ) (f k) * u ((GW.Fock.splitCoordinates n 0).symm (k,K))) := by
    filter_upwards [hK] with k hk
    rw [hk, smul_eq_mul]
  refine ⟨hi.congr hprod, ?_⟩
  exact hvalue.trans (integral_congr_ae hprod)

theorem smeared_annihilation_sector_integral (f : GW.OnePhonon) (n : ℕ)
    (u : GW.Fock.Sector (n+1)) :
    ∀ᵐ K ∂GW.Fock.sectorMeasure n,
      Integrable (fun k : GW.Space => (starRingEnd ℂ) (f k) *
        GW.Fock.sectorInclusion n u ((GW.Fock.splitCoordinates n 0).symm (k,K))) volume ∧
      physicalSector n
        (GW.Fock.sectorAnnihilation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n u) K =
        (Real.sqrt (n+1 : ℕ) : ℂ) * (∫ k : GW.Space, (starRingEnd ℂ) (f k) *
          GW.Fock.sectorInclusion n u ((GW.Fock.splitCoordinates n 0).symm (k,K))) := by
  let J : GW.Fock.Sector n →ₗᵢ[ℂ] GW.Fock.AmbientSector n := physicalSector n
  have hJ : GW.Fock.amplify volume J.toContinuousLinearMap (sectorCurrying n u) =
      rawSectorCurrying n u := by
    apply Lp.ext
    filter_upwards [GW.Fock.amplify_ae volume J.toContinuousLinearMap (sectorCurrying n u),
      sectorCurrying_kernelRepresentative_ae n u] with k hk hr
    exact hk.trans ((kernelRepresentative_physical n _).symm.trans hr)
  have he : physicalSector n
      (GW.Fock.sectorAnnihilation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n u) =
      (Real.sqrt (n+1 : ℕ) : ℂ) •
        GW.Fock.contraction volume f (ambientCurrying n (GW.Fock.sectorInclusion n u)) := by
    rw [ordinarySectorAnnihilation_contraction]
    change J.toContinuousLinearMap (GW.Fock.contraction volume f
      ((Real.sqrt (n+1 : ℕ) : ℂ) • sectorCurrying n u)) = _
    rw [contraction_natural, map_smul, hJ, map_smul]
    rfl
  rw [he]
  filter_upwards [ambient_contraction_sections f n (GW.Fock.sectorInclusion n u),
    Lp.coeFn_smul (Real.sqrt (n+1 : ℕ) : ℂ)
      (GW.Fock.contraction volume f (ambientCurrying n (GW.Fock.sectorInclusion n u)))] with K hK hs
  refine ⟨hK.1, ?_⟩
  simpa only [Pi.smul_apply, smul_eq_mul, hK.2] using hs

end Froehlich
