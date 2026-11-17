import Froehlich.Nodes.GW02
import GW.Fock.Bochner
import GW.Fock.FockGeneralizedBounds

/-! GW03: use the retained complete number graph carrier and its reciprocal embedding. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal

namespace Froehlich

abbrev NumberFormSpace := GW.Fock.NumberGraphCarrier GW.Fock.Sector (1/2)

def numberFormGraph : GW.Spaces.WeightedGraph GW.Fock.Carrier NumberFormSpace :=
  GW.Fock.numberWeightedGraph GW.Fock.Sector (1/2) (by positivity)

def numberFormEmbedding : NumberFormSpace →L[ℂ] GW.Fock.Carrier :=
  numberFormGraph.embedding

theorem numberFormEmbedding_apply (x : NumberFormSpace) (n : ℕ) :
    numberFormEmbedding x n =
      (↑(((n : ℝ)+1)^(-(1/2 : ℝ))) : ℂ) • (show GW.Fock.Carrier from x) n :=
  GW.Fock.numberGraphEmbedding_apply GW.Fock.Sector (1/2) (by positivity) x n

theorem numberFormEmbedding_sqrt_apply (x : NumberFormSpace) (n : ℕ) :
    numberFormEmbedding x n =
      (((Real.sqrt ((n : ℝ)+1))⁻¹ : ℝ) : ℂ) • (show GW.Fock.Carrier from x) n := by
  rw [numberFormEmbedding_apply, Real.rpow_neg (by positivity : 0 ≤ (n : ℝ)+1),
    Real.sqrt_eq_rpow]

theorem numberFormEmbedding_injective : Function.Injective numberFormEmbedding :=
  numberFormGraph.embedding_injective

theorem numberFormEmbedding_dense : DenseRange numberFormEmbedding :=
  numberFormGraph.embedding_dense

theorem numberFormEmbedding_opNorm : ‖numberFormEmbedding‖ ≤ 1 :=
  numberFormGraph.embedding_norm_le

theorem numberFormEmbedding_range : Set.range numberFormEmbedding =
    ((GW.Fock.numberPower GW.Fock.Sector (1/2)).domain : Set GW.Fock.Carrier) := by
  change Set.range (GW.Fock.scalarReciprocal GW.Fock.Sector
    (fun n => ((n : ℝ)+1)^(1/2 : ℝ)) (GW.Fock.shiftedNumber_weight_one (1/2) (by positivity))) = _
  rw [GW.Fock.scalarReciprocal_range,
    GW.Fock.numberPower_domain_eq GW.Fock.Sector (1/2) (by positivity)]
  rfl

def numberFormRootInput (x : NumberFormSpace) :
    (GW.Fock.numberPower GW.Fock.Sector (1/2)).domain :=
  ⟨numberFormEmbedding x, numberFormEmbedding_range.subset ⟨x, rfl⟩⟩

theorem numberFormEmbedding_weighted_norm (x : NumberFormSpace) :
    ‖x‖ ^ 2 = ∑' n : ℕ, ((n : ℝ)+1) * ‖numberFormEmbedding x n‖ ^ 2 := by
  have he : GW.Fock.scalarDiagonal GW.Fock.Sector (fun n => ((n : ℝ)+1)^(1/2 : ℝ))
      ⟨numberFormEmbedding x, numberFormGraph.embedding_mem x⟩ = (show GW.Fock.Carrier from x) :=
    numberFormGraph.product_embedding x
  have h := GW.Fock.scalarDiagonal_norm_sq GW.Fock.Sector
    (fun n => ((n : ℝ)+1)^(1/2 : ℝ)) ⟨numberFormEmbedding x, numberFormGraph.embedding_mem x⟩
  rw [he] at h
  simp_rw [GW.Fock.rpow_square _ _ (by positivity : 0 ≤ (Nat.cast _ : ℝ)+1)] at h
  norm_num at h
  exact h

theorem numberFormRoot_norm (x : NumberFormSpace) :
    ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput x)‖ ^ 2 =
      ∑' n : ℕ, (n : ℝ) * ‖numberFormEmbedding x n‖ ^ 2 := by
  have h := GW.Fock.numberPower_norm_sq GW.Fock.Sector (1/2)
    (by norm_num : (1/2 : ℝ) ≠ 0) (numberFormRootInput x)
  simp_rw [GW.Fock.rpow_square _ _ (Nat.cast_nonneg _)] at h
  norm_num at h
  exact h

theorem numberFormRoot_summable (x : NumberFormSpace) :
    Summable (fun n : ℕ => (n : ℝ) * ‖numberFormEmbedding x n‖ ^ 2) := by
  have h := (GW.Fock.numberPower_domain GW.Fock.Sector (1/2)
    (by positivity) (numberFormEmbedding x)).mp (numberFormRootInput x).property
  norm_num at h
  exact h

theorem numberForm_norm_identity (x : NumberFormSpace) :
    ‖x‖ ^ 2 = ‖numberFormEmbedding x‖ ^ 2 +
      ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput x)‖ ^ 2 := by
  have hu := (GW.Analysis.memℓp_two_iff_sq _).mp (numberFormEmbedding x).property
  rw [numberFormEmbedding_weighted_norm, numberFormRoot_norm, GW.Fock.carrier_norm_sq]
  have he : (fun n : ℕ => ((n : ℝ)+1) * ‖numberFormEmbedding x n‖ ^ 2) =
      (fun n : ℕ => ‖numberFormEmbedding x n‖ ^ 2 + (n : ℝ) * ‖numberFormEmbedding x n‖ ^ 2) := by
    funext n
    ring
  rw [he]
  exact Summable.tsum_add hu (numberFormRoot_summable x)

/-- One output sector of the momentum-indexed annihilation field, on number coordinates. -/
def annihilationSector (n : ℕ) : NumberFormSpace →L[ℂ]
    Lp (GW.Fock.Sector n) 2 (volume : Measure GW.Space) :=
  (Real.sqrt (n+1 : ℕ) : ℂ) • (sectorCurrying n).comp
    ((lp.evalCLM ℂ GW.Fock.Sector 2 (n+1)).comp numberFormEmbedding)

theorem annihilationSector_norm_sq (n : ℕ) (x : NumberFormSpace) :
    ‖annihilationSector n x‖ ^ 2 =
      ((n+1 : ℕ) : ℝ) * ‖numberFormEmbedding x (n+1)‖ ^ 2 := by
  change ‖(Real.sqrt (n+1 : ℕ) : ℂ) • sectorCurrying n (numberFormEmbedding x (n+1))‖ ^ 2 = _
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (Nat.cast_nonneg (n+1)), sectorCurrying_norm]

theorem annihilationSectors_mem (x : NumberFormSpace) :
    Memℓp (fun n => annihilationSector n x) 2 := by
  apply (GW.Analysis.memℓp_two_iff_sq _).mpr
  simp_rw [annihilationSector_norm_sq]
  exact (summable_nat_add_iff 1).mpr (numberFormRoot_summable x)

def annihilationSectorsLinear : NumberFormSpace →ₗ[ℂ]
    GW.Fock.BochnerSectorSum (volume : Measure GW.Space) GW.Fock.Sector where
  toFun x := ⟨fun n => annihilationSector n x, annihilationSectors_mem x⟩
  map_add' x y := by
    apply lp.ext
    funext n
    exact (annihilationSector n).map_add x y
  map_smul' c x := by
    apply lp.ext
    funext n
    exact (annihilationSector n).map_smul c x

theorem annihilationSectors_norm_sq (x : NumberFormSpace) :
    ‖annihilationSectorsLinear x‖ ^ 2 =
      ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput x)‖ ^ 2 := by
  rw [GW.Analysis.lp_norm_sq, numberFormRoot_norm]
  change (∑' n : ℕ, ‖annihilationSector n x‖ ^ 2) = _
  simp_rw [annihilationSector_norm_sq]
  have h := (numberFormRoot_summable x).tsum_eq_zero_add
  simpa only [Nat.cast_zero, zero_mul, zero_add] using h.symm

def annihilationFieldLinear : NumberFormSpace →ₗ[ℂ]
    Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) :=
  (GW.Fock.bochnerUnitary volume GW.Fock.Sector).toLinearMap.comp annihilationSectorsLinear

theorem annihilationFieldLinear_norm_sq (x : NumberFormSpace) :
    ‖annihilationFieldLinear x‖ ^ 2 =
      ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput x)‖ ^ 2 := by
  change ‖GW.Fock.bochnerUnitary volume GW.Fock.Sector (annihilationSectorsLinear x)‖ ^ 2 = _
  rw [LinearIsometryEquiv.norm_map]
  exact annihilationSectors_norm_sq x

theorem annihilationFieldLinear_bound (x : NumberFormSpace) :
    ‖annihilationFieldLinear x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [annihilationFieldLinear_norm_sq]
  have h := numberForm_norm_identity x
  nlinarith [sq_nonneg ‖numberFormEmbedding x‖]

/-- The specified field on the complete number-form carrier, not an operator at a fixed k. -/
def annihilationField : NumberFormSpace →L[ℂ]
    Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) :=
  annihilationFieldLinear.mkContinuous 1
    (fun x => by simpa only [one_mul] using annihilationFieldLinear_bound x)

theorem annihilationField_norm_sq (x : NumberFormSpace) :
    ‖annihilationField x‖ ^ 2 =
      ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput x)‖ ^ 2 :=
  annihilationFieldLinear_norm_sq x

theorem annihilationField_opNorm : ‖annihilationField‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖annihilationFieldLinear x‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using annihilationFieldLinear_bound x

theorem annihilationField_component (x : NumberFormSpace) (n : ℕ) :
    GW.Fock.bochnerCoordinate volume GW.Fock.Sector n (annihilationField x) = annihilationSector n x :=
  GW.Fock.bochnerCoordinate_unitary volume GW.Fock.Sector (annihilationSectorsLinear x) n

theorem annihilationField_common_ae (x : NumberFormSpace) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∀ n, (annihilationField x k) n = annihilationSector n x k :=
  GW.Fock.bochnerReconstruct_ae volume GW.Fock.Sector (annihilationSectorsLinear x)

theorem annihilationField_scaled_common_ae (x : NumberFormSpace) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∀ n,
      (annihilationField x k) n = (Real.sqrt (n+1 : ℕ) : ℂ) •
        sectorCurrying n (numberFormEmbedding x (n+1)) k := by
  have hs (n : ℕ) : ∀ᵐ k ∂(volume : Measure GW.Space), annihilationSector n x k =
      (Real.sqrt (n+1 : ℕ) : ℂ) • sectorCurrying n (numberFormEmbedding x (n+1)) k :=
    Lp.coeFn_smul (Real.sqrt (n+1 : ℕ) : ℂ) (sectorCurrying n (numberFormEmbedding x (n+1)))
  filter_upwards [annihilationField_common_ae x, ae_all_iff.mpr hs] with k hk hs₀
  exact fun n => (hk n).trans (hs₀ n)

theorem annihilationField_representative_common_ae (x : NumberFormSpace) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∀ n,
      (GW.Fock.kernelFixedInclusion n
        (GW.Fock.ordinarySectorKernel n ((annihilationField x k) n)) : GW.Fock.AmbientSector n) =ᵐ[GW.Fock.sectorMeasure n]
          (fun K => (Real.sqrt (n+1 : ℕ) : ℂ) •
            GW.Fock.sectorInclusion n (numberFormEmbedding x (n+1))
              ((GW.Fock.splitCoordinates n 0).symm (k,K))) := by
  have hs (n : ℕ) := sectorCurrying_sections n (numberFormEmbedding x (n+1))
  filter_upwards [annihilationField_scaled_common_ae x, ae_all_iff.mpr hs] with k hk hs₀
  intro n
  rw [hk n, map_smul, map_smul]
  exact (Lp.coeFn_smul (Real.sqrt (n+1 : ℕ) : ℂ)
    (GW.Fock.kernelFixedInclusion n (GW.Fock.ordinarySectorKernel n
      (sectorCurrying n (numberFormEmbedding x (n+1)) k)))).trans
        ((hs₀ n).mono (fun K hK => congrArg ((Real.sqrt (n+1 : ℕ) : ℂ) • ·) hK))

theorem sectorCurrying_oneParticle (f : GW.OnePhonon) :
    sectorCurrying 0 (oneParticleCoordinate f) = f := by
  apply Lp.ext
  have hi : (GW.Fock.sectorInclusion 0 (oneParticleCoordinate f) : GW.Fock.Coordinates 1 → ℂ) =ᵐ[GW.Fock.sectorMeasure 1]
      (fun K => f (K 0)) := by
    rw [oneParticleCoordinate_representative]
    exact Lp.coeFn_compMeasurePreserving f GW.Fock.oneBosonCoordinate_preserving
  have ht := Measure.ae_ae_of_ae_prod
    ((GW.Fock.splitCoordinates_inverse_preserving 0 0).quasiMeasurePreserving.ae hi)
  filter_upwards [sectorCurrying_sections 0 (oneParticleCoordinate f), ht] with k hk ht₀
  let a : ℂ := sectorCurrying 0 (oneParticleCoordinate f) k
  have he : ∀ᵐ K ∂GW.Fock.sectorMeasure 0, a = f k := by
    filter_upwards [hk, ht₀, GW.Fock.vacuumAdapter_ae a] with K h₁ h₂ h₃
    have hz := congrArg (fun t : GW.Fock.AmbientSector 0 => t K) (kernelRepresentative_zero a)
    exact h₃.symm.trans (hz.symm.trans (h₁.trans (h₂.trans
      (congrArg f (GW.Fock.insertCoordinate_same 0 0 k K)))))
  obtain ⟨K, hK⟩ := he.exists
  exact hK

/-- Actual physical one-particle input, with its proved shifted-number domain witness. -/
def numberOneParticleInput (f : GW.OnePhonon) : numberFormGraph.domain :=
  ⟨oneParticleInclusion f,
    GW.Fock.scalarDiagonal_single_mem GW.Fock.Sector
      (fun n => ((n : ℝ)+1)^(1/2 : ℝ)) 1 (oneParticleCoordinate f)⟩

/-- Coordinates of the physical vector `oneParticleInclusion f`; its coordinate-one
weight is √2, so this is not the underlying unweighted inclusion. -/
def numberOneParticleLift (f : GW.OnePhonon) : NumberFormSpace :=
  numberFormGraph.product (numberOneParticleInput f)

theorem numberFormEmbedding_oneParticleLift (f : GW.OnePhonon) :
    numberFormEmbedding (numberOneParticleLift f) = oneParticleInclusion f :=
  numberFormGraph.embedding_product (numberOneParticleInput f)

/-- Explicit type bridge for the existing scalar vacuum sector in Bochner L². -/
def zeroSectorField (f : GW.OnePhonon) : Lp (GW.Fock.Sector 0) 2 (volume : Measure GW.Space) := f

theorem annihilationSectors_oneParticle (f : GW.OnePhonon) :
    annihilationSectorsLinear (numberOneParticleLift f) =
      lp.single (E := fun n => Lp (GW.Fock.Sector n) 2 (volume : Measure GW.Space)) 2 0 (zeroSectorField f) := by
  apply lp.ext
  funext n
  change (Real.sqrt (n+1 : ℕ) : ℂ) •
    sectorCurrying n (numberFormEmbedding (numberOneParticleLift f) (n+1)) =
      (lp.single (E := fun n => Lp (GW.Fock.Sector n) 2 (volume : Measure GW.Space)) 2 0 (zeroSectorField f)) n
  rw [numberFormEmbedding_oneParticleLift, oneParticleInclusion_apply]
  by_cases hn : n = 0
  · subst n
    rw [lp.single_apply_self, lp.single_apply_self]
    simp only [Nat.zero_add, Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, one_smul]
    change sectorCurrying 0 (oneParticleCoordinate f) =
      (show Lp (GW.Fock.Sector 0) 2 (volume : Measure GW.Space) from f)
    exact sectorCurrying_oneParticle f
  · rw [lp.single_apply_ne _ _ _ (show n+1 ≠ 1 by omega), map_zero, smul_zero,
      lp.single_apply_ne _ _ _ hn]

theorem annihilationField_oneParticle (f : GW.OnePhonon) :
    annihilationField (numberOneParticleLift f) =
      (lp.singleContinuousLinearMap ℂ GW.Fock.Sector 2 0).compLp (zeroSectorField f) := by
  change GW.Fock.bochnerUnitary volume GW.Fock.Sector
    (annihilationSectorsLinear (numberOneParticleLift f)) = _
  rw [annihilationSectors_oneParticle]
  exact GW.Fock.bochnerUnitary_single volume GW.Fock.Sector 0 (zeroSectorField f)

theorem annihilationField_oneParticle_ae (f : GW.OnePhonon) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      annihilationField (numberOneParticleLift f) k = f k • GW.Fock.vacuum := by
  rw [annihilationField_oneParticle]
  filter_upwards [(lp.singleContinuousLinearMap ℂ GW.Fock.Sector 2 0).coeFn_compLp (zeroSectorField f)] with k hk
  rw [hk]
  change lp.single (E := GW.Fock.Sector) 2 0 (show GW.Fock.Sector 0 from f k) =
    f k • lp.single (E := GW.Fock.Sector) 2 0 (show GW.Fock.Sector 0 from (1 : ℂ))
  rw [← lp.single_smul]
  congr 1
  change f k = f k * (1 : ℂ)
  exact (mul_one _).symm

def numberVacuumLift : NumberFormSpace :=
  GW.Fock.numberGraphCopy GW.Fock.Sector (1/2) GW.Fock.vacuum

theorem numberFormEmbedding_vacuum : numberFormEmbedding numberVacuumLift = GW.Fock.vacuum := by
  apply lp.ext
  funext n
  rw [numberFormEmbedding_apply]
  change (↑(((n : ℝ)+1)^(-(1/2 : ℝ))) : ℂ) • GW.Fock.vacuum n = GW.Fock.vacuum n
  cases n with
  | zero =>
    simp only [GW.Fock.vacuum_zero, Nat.cast_zero, zero_add, Real.one_rpow, Complex.ofReal_one]
    change (1 : ℂ) * (1 : ℂ) = 1
    exact one_mul 1
  | succ n => simp [GW.Fock.vacuum_succ]

theorem annihilationField_of_vacuum (x : NumberFormSpace)
    (hx : numberFormEmbedding x = GW.Fock.vacuum) : annihilationField x = 0 := by
  apply GW.Fock.bochnerCoordinate_ext volume GW.Fock.Sector
  intro n
  rw [annihilationField_component, map_zero]
  change (Real.sqrt (n+1 : ℕ) : ℂ) • sectorCurrying n (numberFormEmbedding x (n+1)) = 0
  rw [hx, GW.Fock.vacuum_succ, map_zero, smul_zero]

theorem annihilationField_vacuum : annihilationField numberVacuumLift = 0 :=
  annihilationField_of_vacuum numberVacuumLift numberFormEmbedding_vacuum

/-- Particle selection on number coordinates uses exactly the retained coordinate selection. -/
def numberFormCutoff (m : ℕ) : NumberFormSpace →L[ℂ] NumberFormSpace := by
  change GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier
  exact GW.Fock.P m

def numberFormHighProjection (m : ℕ) : NumberFormSpace →L[ℂ] NumberFormSpace := by
  change GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier
  exact highSectorProjection m

theorem numberFormEmbedding_cutoff (m : ℕ) (x : NumberFormSpace) :
    numberFormEmbedding (numberFormCutoff m x) = GW.Fock.P m (numberFormEmbedding x) := by
  apply lp.ext
  funext n
  rw [numberFormEmbedding_apply]
  change (↑(((n : ℝ)+1)^(-(1/2 : ℝ))) : ℂ) •
    GW.Fock.cutoff GW.Fock.Sector m (show GW.Fock.Carrier from x) n =
      GW.Fock.cutoff GW.Fock.Sector m (numberFormEmbedding x) n
  rw [GW.Fock.cutoff_apply, GW.Fock.cutoff_apply]
  by_cases hn : n ≤ m
  · simp only [if_pos hn]
    exact (numberFormEmbedding_apply x n).symm
  · simp only [if_neg hn, smul_zero]

theorem numberFormEmbedding_highProjection (m : ℕ) (x : NumberFormSpace) :
    numberFormEmbedding (numberFormHighProjection m x) =
      highSectorProjection m (numberFormEmbedding x) := by
  cases m with
  | zero => rfl
  | succ m =>
    change numberFormEmbedding (x - numberFormCutoff m x) =
      numberFormEmbedding x - GW.Fock.P m (numberFormEmbedding x)
    rw [map_sub, numberFormEmbedding_cutoff]

theorem annihilationSectors_cutoff (m : ℕ) (x : NumberFormSpace) :
    annihilationSectorsLinear (numberFormCutoff (m+1) x) =
      GW.Fock.cutoff (fun n => Lp (GW.Fock.Sector n) 2 (volume : Measure GW.Space)) m
        (annihilationSectorsLinear x) := by
  apply lp.ext
  funext n
  change (Real.sqrt (n+1 : ℕ) : ℂ) •
    sectorCurrying n (numberFormEmbedding (numberFormCutoff (m+1) x) (n+1)) = _
  rw [numberFormEmbedding_cutoff]
  change (Real.sqrt (n+1 : ℕ) : ℂ) •
    sectorCurrying n (GW.Fock.cutoff GW.Fock.Sector (m+1) (numberFormEmbedding x) (n+1)) =
      GW.Fock.cutoff (fun n => Lp (GW.Fock.Sector n) 2 (volume : Measure GW.Space)) m
        (annihilationSectorsLinear x) n
  rw [GW.Fock.cutoff_apply, GW.Fock.cutoff_apply]
  by_cases hn : n ≤ m
  · simp only [if_pos hn, if_pos (show n+1 ≤ m+1 by omega)]
    rfl
  · simp only [if_neg hn, if_neg (show ¬n+1 ≤ m+1 by omega), map_zero, smul_zero]

theorem annihilationSectors_cutoff_zero (x : NumberFormSpace) :
    annihilationSectorsLinear (numberFormCutoff 0 x) = 0 := by
  apply lp.ext
  funext n
  change (Real.sqrt (n+1 : ℕ) : ℂ) •
    sectorCurrying n (numberFormEmbedding (numberFormCutoff 0 x) (n+1)) = 0
  rw [numberFormEmbedding_cutoff, GW.Fock.cutoff_apply]
  simp only [if_neg (show ¬n+1 ≤ 0 by omega), map_zero, smul_zero]

theorem annihilationField_cutoff (m : ℕ) (x : NumberFormSpace) :
    annihilationField (numberFormCutoff (m+1) x) =
      (GW.Fock.P m).compLp (annihilationField x) := by
  change GW.Fock.bochnerUnitary volume GW.Fock.Sector
    (annihilationSectorsLinear (numberFormCutoff (m+1) x)) =
      (GW.Fock.cutoff GW.Fock.Sector m).compLp
        (GW.Fock.bochnerUnitary volume GW.Fock.Sector (annihilationSectorsLinear x))
  rw [annihilationSectors_cutoff, GW.Fock.bochnerUnitary_cutoff]

theorem annihilationField_cutoff_zero (x : NumberFormSpace) :
    annihilationField (numberFormCutoff 0 x) = 0 := by
  change GW.Fock.bochnerUnitary volume GW.Fock.Sector
    (annihilationSectorsLinear (numberFormCutoff 0 x)) = 0
  rw [annihilationSectors_cutoff_zero, map_zero]

/-- Exact source projection law, with input at least m+1 and output at least m. -/
theorem annihilationField_highProjection (m : ℕ) (x : NumberFormSpace) :
    annihilationField (numberFormHighProjection (m+1) x) =
      (highSectorProjection m).compLp (annihilationField x) := by
  cases m with
  | zero =>
    change annihilationField (x - numberFormCutoff 0 x) =
      (highSectorProjection 0).compLp (annihilationField x)
    rw [map_sub, annihilationField_cutoff_zero, sub_zero]
    apply Lp.ext
    filter_upwards [(highSectorProjection 0).coeFn_compLp (annihilationField x)] with k hk
    exact hk.symm
  | succ m =>
    change annihilationField (x - numberFormCutoff (m+1) x) =
      (highSectorProjection (m+1)).compLp (annihilationField x)
    rw [map_sub, annihilationField_cutoff]
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (annihilationField x) ((GW.Fock.P m).compLp (annihilationField x)),
      (GW.Fock.P m).coeFn_compLp (annihilationField x),
      (highSectorProjection (m+1)).coeFn_compLp (annihilationField x)] with k hs hp hh
    rw [hs, Pi.sub_apply, hp, hh]
    rfl

theorem annihilationField_highProjection_ae (m : ℕ) (x : NumberFormSpace) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      annihilationField (numberFormHighProjection (m+1) x) k =
        highSectorProjection m (annihilationField x k) := by
  rw [annihilationField_highProjection]
  exact (highSectorProjection m).coeFn_compLp (annihilationField x)

theorem annihilationField_of_oneParticle (x : NumberFormSpace) (f : GW.OnePhonon)
    (hx : numberFormEmbedding x = oneParticleInclusion f) :
    ∀ᵐ k ∂(volume : Measure GW.Space), annihilationField x k = f k • GW.Fock.vacuum := by
  have he : x = numberOneParticleLift f :=
    numberFormEmbedding_injective (hx.trans (numberFormEmbedding_oneParticleLift f).symm)
  rw [he]
  exact annihilationField_oneParticle_ae f

end Froehlich
