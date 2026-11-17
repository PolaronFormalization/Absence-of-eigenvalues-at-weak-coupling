module
public import GW.Fock.FockGeneralized
@[expose] public section
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace Froehlich

/-- The one-variable coordinate map prescribed in GW01, with no normalization factor. -/
def oneParticleCoordinate : GW.OnePhonon ≃ₗᵢ[ℂ] GW.Fock.Sector 1 :=
  (GW.Fock.kernelOneBoson (E := ℂ)).trans (GW.Fock.ordinarySectorKernel 1).symm

theorem oneParticleCoordinate_representative (f : GW.OnePhonon) :
    GW.Fock.sectorInclusion 0 (oneParticleCoordinate f) =
      Lp.compMeasurePreserving (fun k : GW.Fock.Coordinates 1 => k 0)
        GW.Fock.oneBosonCoordinate_preserving f := by
  have h : GW.Fock.ordinarySectorKernel 1 (oneParticleCoordinate f) =
      GW.Fock.kernelOneBoson f :=
    (GW.Fock.ordinarySectorKernel 1).apply_symm_apply _
  have hc := congrArg (fun v : GW.Fock.kernelFixed (E := ℂ) 1 =>
    (v : GW.Fock.KernelSector ℂ 1)) h
  change GW.Fock.sectorInclusion 0 (oneParticleCoordinate f) =
    (GW.Fock.kernelOneBoson f : GW.Fock.KernelSector ℂ 1) at hc
  rw [GW.Fock.kernelOneBoson_coe, GW.Fock.kernelSplit_vacuum_one] at hc
  exact hc

/-- Scalar vacuum inclusion into the retained GW Hilbert sum. -/
def vacuumInclusion : ℂ →L[ℂ] GW.Fock.Carrier :=
  lp.singleContinuousLinearMap ℂ GW.Fock.Sector 2 0

/-- The one-particle inclusion into the retained GW Hilbert sum. -/
def oneParticleInclusion : GW.OnePhonon →L[ℂ] GW.Fock.Carrier :=
  (lp.singleContinuousLinearMap ℂ GW.Fock.Sector 2 1).comp
    oneParticleCoordinate.toLinearIsometry.toContinuousLinearMap

/-- The physical one-particle coordinate extracted from the retained GW Hilbert sum. -/
def oneParticleExtraction : GW.Fock.Carrier →L[ℂ] GW.OnePhonon :=
  oneParticleCoordinate.symm.toLinearIsometry.toContinuousLinearMap.comp
    (lp.evalCLM ℂ GW.Fock.Sector 2 1)

theorem vacuumInclusion_one : vacuumInclusion 1 = GW.Fock.vacuum := rfl

theorem vacuumInclusion_norm (z : ℂ) : ‖vacuumInclusion z‖ = ‖z‖ :=
  lp.norm_single (E := GW.Fock.Sector) (by norm_num : (0 : ℝ≥0∞) < 2) 0 z

theorem oneParticleInclusion_apply (f : GW.OnePhonon) :
    oneParticleInclusion f = lp.single 2 1 (oneParticleCoordinate f) := rfl

theorem oneParticleExtraction_apply (u : GW.Fock.Carrier) :
    oneParticleExtraction u = oneParticleCoordinate.symm (u 1) := rfl

theorem oneParticleInclusion_norm (f : GW.OnePhonon) :
    ‖oneParticleInclusion f‖ = ‖f‖ := by
  rw [oneParticleInclusion_apply,
    lp.norm_single (E := GW.Fock.Sector) (by norm_num : (0 : ℝ≥0∞) < 2)]
  exact oneParticleCoordinate.norm_map f

theorem oneParticleExtraction_inclusion (f : GW.OnePhonon) :
    oneParticleExtraction (oneParticleInclusion f) = f := by
  change oneParticleCoordinate.symm ((lp.single 2 1 (oneParticleCoordinate f)) 1) = f
  rw [lp.single_apply_self, LinearIsometryEquiv.symm_apply_apply]

theorem oneParticleInclusion_pairing (f : GW.OnePhonon) (u : GW.Fock.Carrier) :
    ⟪oneParticleInclusion f, u⟫_ℂ = ⟪f, oneParticleExtraction u⟫_ℂ := by
  rw [oneParticleInclusion_apply, lp.inner_single_left]
  exact oneParticleCoordinate.inner_map_eq_flip f (u 1)

theorem oneParticleInclusion_adjoint :
    oneParticleInclusion.adjoint = oneParticleExtraction := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u f
  simpa only [inner_conj_symm] using
    congrArg (starRingEnd ℂ) (oneParticleInclusion_pairing f u).symm

theorem vacuumInclusion_pairing (z : ℂ) (u : GW.Fock.Carrier) :
    ⟪vacuumInclusion z, u⟫_ℂ = ⟪z, u 0⟫_ℂ :=
  lp.inner_single_left 0 z u

/-- Exact particle-number projection, on the canonical GW carrier. -/
def sectorProjection (n : ℕ) : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  (lp.singleContinuousLinearMap ℂ GW.Fock.Sector 2 n).comp
    (lp.evalCLM ℂ GW.Fock.Sector 2 n)

theorem sectorProjection_apply (n : ℕ) (u : GW.Fock.Carrier) :
    sectorProjection n u = lp.single 2 n (u n) := rfl

theorem sectorProjection_norm_le (n : ℕ) (u : GW.Fock.Carrier) :
    ‖sectorProjection n u‖ ≤ ‖u‖ := by
  rw [sectorProjection_apply,
    lp.norm_single (E := GW.Fock.Sector) (by norm_num : (0 : ℝ≥0∞) < 2)]
  exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) u n

theorem sectorProjection_opNorm_le (n : ℕ) : ‖sectorProjection n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using sectorProjection_norm_le n u

theorem sectorProjection_idempotent (n : ℕ) :
    (sectorProjection n).comp (sectorProjection n) = sectorProjection n := by
  ext u k
  change (lp.single 2 n ((lp.single 2 n (u n)) n)) k = (lp.single 2 n (u n)) k
  rw [lp.single_apply_self]

theorem sectorProjection_pairing (n : ℕ) (u v : GW.Fock.Carrier) :
    ⟪sectorProjection n u, v⟫_ℂ = ⟪u, sectorProjection n v⟫_ℂ := by
  rw [sectorProjection_apply, sectorProjection_apply, lp.inner_single_left,
    lp.inner_single_right]

theorem sectorProjection_adjoint (n : ℕ) :
    (sectorProjection n).adjoint = sectorProjection n := by
  apply Eq.symm
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr (sectorProjection_pairing n)

theorem oneParticleInclusion_extraction (u : GW.Fock.Carrier) :
    oneParticleInclusion (oneParticleExtraction u) = sectorProjection 1 u := by
  change lp.single 2 1 (oneParticleCoordinate (oneParticleCoordinate.symm (u 1))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- The prescribed finite particle cutoff is reused unchanged. -/
abbrev lowSectorProjection (m : ℕ) := GW.Fock.P m

theorem lowSectorProjection_norm_le (m : ℕ) (u : GW.Fock.Carrier) :
    ‖lowSectorProjection m u‖ ≤ ‖u‖ := GW.Fock.cutoff_norm_le GW.Fock.Sector m u

theorem lowSectorProjection_idempotent (m : ℕ) :
    (lowSectorProjection m).comp (lowSectorProjection m) = lowSectorProjection m :=
  GW.Fock.cutoff_idempotent GW.Fock.Sector m

theorem lowSectorProjection_pairing (m : ℕ) (u v : GW.Fock.Carrier) :
    ⟪lowSectorProjection m u, v⟫_ℂ = ⟪u, lowSectorProjection m v⟫_ℂ :=
  GW.Fock.cutoff_pairing GW.Fock.Sector m u v

/-- Complementary particle projection, including the special case `m = 0`. -/
def highSectorProjection : ℕ → (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier)
  | 0 => ContinuousLinearMap.id ℂ GW.Fock.Carrier
  | m + 1 => ContinuousLinearMap.id ℂ GW.Fock.Carrier - GW.Fock.P m

theorem highSectorProjection_apply (m : ℕ) (u : GW.Fock.Carrier) (n : ℕ) :
    highSectorProjection m u n = if m ≤ n then u n else 0 := by
  cases m with
  | zero => simp [highSectorProjection]
  | succ m =>
    change u n - GW.Fock.cutoff GW.Fock.Sector m u n = _
    rw [GW.Fock.cutoff_apply]
    by_cases hn : n ≤ m
    · simp [hn, show ¬m + 1 ≤ n by omega]
    · simp [hn, show m + 1 ≤ n by omega]

theorem highSectorProjection_norm_le (m : ℕ) (u : GW.Fock.Carrier) :
    ‖highSectorProjection m u‖ ≤ ‖u‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  rw [highSectorProjection_apply]
  split_ifs <;> simp only [le_refl, norm_zero, norm_nonneg]

theorem highSectorProjection_opNorm_le (m : ℕ) : ‖highSectorProjection m‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using highSectorProjection_norm_le m u

theorem highSectorProjection_idempotent (m : ℕ) :
    (highSectorProjection m).comp (highSectorProjection m) = highSectorProjection m := by
  ext u n
  change highSectorProjection m (highSectorProjection m u) n = highSectorProjection m u n
  by_cases hn : m ≤ n <;> simp [highSectorProjection_apply, hn]

theorem highSectorProjection_pairing (m : ℕ) (u v : GW.Fock.Carrier) :
    ⟪highSectorProjection m u, v⟫_ℂ = ⟪u, highSectorProjection m v⟫_ℂ := by
  cases m with
  | zero => rfl
  | succ m =>
    change ⟪u - GW.Fock.P m u, v⟫_ℂ = ⟪u, v - GW.Fock.P m v⟫_ℂ
    rw [inner_sub_left, inner_sub_right, GW.Fock.cutoff_pairing]

theorem highSectorProjection_adjoint (m : ℕ) :
    (highSectorProjection m).adjoint = highSectorProjection m := by
  apply Eq.symm
  exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr (highSectorProjection_pairing m)

end Froehlich
