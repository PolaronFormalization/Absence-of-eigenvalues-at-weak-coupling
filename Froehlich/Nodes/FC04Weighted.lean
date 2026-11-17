import Froehlich.Nodes.FC04

/-! Constructive moving-energy sector classes from actual free operator graph
coordinates. The product unitary provides their Bochner measurability. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem movingEnergyWeight_measurable (P : GW.Space) (n : ℕ) :
    Measurable (fun p : GW.Space × GW.Fock.Coordinates n => energyWeight (P-p.1) n p.2) := by
  unfold energyWeight freeSymbol
  exact (measurable_const.add
    (((((totalMomentum_measurable n).comp measurable_snd).sub
      (measurable_const.sub measurable_fst)).norm.pow_const (2 : ℕ)).add measurable_const)).sqrt

theorem movingEnergySection_memLp (P : GW.Space) (x : OperatorGraphSpace P) (n : ℕ) :
    MemLp (movingEnergySection P n (physicalSector (n+1) (graphEmbedding P x (n+1)))) 2
      ((volume : Measure GW.Space).prod (GW.Fock.sectorMeasure n)) := by
  let u := physicalSector (n+1) (graphEmbedding P x (n+1))
  let v := physicalSector (n+1) (freeActionOnGraph P x (n+1))
  let e := (GW.Fock.splitCoordinates n 0).symm
  have hv : MemLp (fun p => v (e p)) 2
      ((volume : Measure GW.Space).prod (GW.Fock.sectorMeasure n)) :=
    (Lp.memLp v).comp_measurePreserving (GW.Fock.splitCoordinates_inverse_preserving n 0)
  have hu := (Lp.memLp u).comp_measurePreserving
    (GW.Fock.splitCoordinates_inverse_preserving n 0)
  have hm : AEStronglyMeasurable (movingEnergySection P n u)
      ((volume : Measure GW.Space).prod (GW.Fock.sectorMeasure n)) :=
    (((Complex.continuous_ofReal.measurable.comp (movingEnergyWeight_measurable P n)).aestronglyMeasurable.const_mul (Real.sqrt (n+1 : ℕ) : ℂ)).mul hu.aestronglyMeasurable)
  apply hv.of_le hm
  have hgraph := (GW.Fock.splitCoordinates_inverse_preserving n 0).quasiMeasurePreserving.ae
    (freeActionOnGraph_ae P x (n+1))
  filter_upwards [hgraph] with p hp
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [movingEnergySection_norm_sq]
  change (n+1 : ℝ) * freeSymbol P (n+1) (e p) * ‖u (e p)‖ ^ 2 ≤ ‖v (e p)‖ ^ 2
  have he : (freeSymbol P (n+1) (e p) : ℂ) * u (e p) = v (e p) := by
    simpa only [smul_eq_mul] using hp
  rw [← he, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (freeSymbol_nonneg P (n+1) (e p))]
  exact mul_le_mul_of_nonneg_right (by
    simpa only [movingEnergyWeight_exact] using movingEnergyWeight_numerical P p.1 n p.2)
    (sq_nonneg _)

def movingEnergySectorClass (P : GW.Space) (x : OperatorGraphSpace P) (n : ℕ) :
    Lp ℂ 2 ((volume : Measure GW.Space).prod (GW.Fock.sectorMeasure n)) :=
  (movingEnergySection_memLp P x n).toLp _

theorem movingEnergySectorClass_ae (P : GW.Space) (x : OperatorGraphSpace P) (n : ℕ) :
    movingEnergySectorClass P x n =ᵐ[(volume : Measure GW.Space).prod (GW.Fock.sectorMeasure n)]
      movingEnergySection P n (physicalSector (n+1) (graphEmbedding P x (n+1))) :=
  MemLp.coeFn_toLp _

/-- A genuine strongly measurable Bochner L² class of weighted output sectors. -/
def movingEnergySectorField (P : GW.Space) (x : OperatorGraphSpace P) (n : ℕ) :
    Lp (GW.Fock.AmbientSector n) 2 (volume : Measure GW.Space) :=
  (GW.Fock.productUnitary volume (GW.Fock.sectorMeasure n)).symm
    (movingEnergySectorClass P x n)

theorem movingEnergySectorField_norm_sq (P : GW.Space) (x : OperatorGraphSpace P) (n : ℕ) :
    ‖movingEnergySectorField P x n‖ ^ 2 =
      ∫ K : GW.Fock.Coordinates (n+1), (n+1 : ℝ) * freeSymbol P (n+1) K *
        ‖physicalSector (n+1) (graphEmbedding P x (n+1)) K‖ ^ 2 := by
  rw [movingEnergySectorField, LinearIsometryEquiv.norm_map, GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  calc
    _ = ∫ p : GW.Space × GW.Fock.Coordinates n,
        (n+1 : ℝ) * freeSymbol P (n+1) ((GW.Fock.splitCoordinates n 0).symm p) *
          ‖physicalSector (n+1) (graphEmbedding P x (n+1))
            ((GW.Fock.splitCoordinates n 0).symm p)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [movingEnergySectorClass_ae P x n] with p hp
      rw [hp, movingEnergySection_norm_sq]
    _ = _ := (GW.Fock.splitCoordinates_inverse_preserving n 0).integral_comp'
      (fun K : GW.Fock.Coordinates (n+1) => (n+1 : ℝ) * freeSymbol P (n+1) K *
        ‖physicalSector (n+1) (graphEmbedding P x (n+1)) K‖ ^ 2)

theorem movingEnergySectorField_norm_le (P : GW.Space) (x : OperatorGraphSpace P) (n : ℕ) :
    ‖movingEnergySectorField P x n‖ ≤ ‖freeActionOnGraph P x (n+1)‖ := by
  rw [movingEnergySectorField, LinearIsometryEquiv.norm_map,
    ← (physicalSector (n+1)).norm_map (freeActionOnGraph P x (n+1)),
    ← (GW.Fock.splitUnitary n 0).norm_map]
  apply Lp.norm_le_norm_of_ae_le
  have hgraph := (GW.Fock.splitCoordinates_inverse_preserving n 0).quasiMeasurePreserving.ae
    (freeActionOnGraph_ae P x (n+1))
  filter_upwards [movingEnergySectorClass_ae P x n,
    GW.Fock.splitUnitary_ae n 0 (physicalSector (n+1) (freeActionOnGraph P x (n+1))),
    hgraph] with p hp hv hg
  rw [hp, hv]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [movingEnergySection_norm_sq, ← hg, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (freeSymbol_nonneg P (n+1) _)]
  exact mul_le_mul_of_nonneg_right (by
    simpa only [movingEnergyWeight_exact] using movingEnergyWeight_numerical P p.1 n p.2)
    (sq_nonneg _)

theorem movingEnergySectorFields_summable (P : GW.Space) (x : OperatorGraphSpace P) :
    Summable (fun n => ‖movingEnergySectorField P x n‖ ^ 2) := by
  have hv : Summable (fun n => ‖freeActionOnGraph P x (n+1)‖ ^ 2) :=
    (summable_nat_add_iff 1).mpr
      ((GW.Analysis.memℓp_two_iff_sq _).mp (freeActionOnGraph P x).property)
  exact Summable.of_nonneg_of_le (fun n => sq_nonneg _)
    (fun n => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (movingEnergySectorField_norm_le P x n)) hv

def movingEnergySectorSum (P : GW.Space) (x : OperatorGraphSpace P) :
    GW.Fock.BochnerSectorSum (volume : Measure GW.Space) (fun n => GW.Fock.AmbientSector n) :=
  ⟨fun n => movingEnergySectorField P x n,
    (GW.Analysis.memℓp_two_iff_sq _).mpr (movingEnergySectorFields_summable P x)⟩

/-- Ambient-sector reconstruction is a genuine Bochner class; symmetry and
physical reciprocal-weight identification are proved on this class next. -/
def movingEnergyAmbientField (P : GW.Space) (x : OperatorGraphSpace P) :
    GW.Fock.BochnerFock (volume : Measure GW.Space) (fun n => GW.Fock.AmbientSector n) :=
  GW.Fock.bochnerUnitary (volume : Measure GW.Space) (fun n => GW.Fock.AmbientSector n)
    (movingEnergySectorSum P x)

theorem movingEnergyAmbientField_norm_sq (P : GW.Space) (x : OperatorGraphSpace P) :
    ‖movingEnergyAmbientField P x‖ ^ 2 =
      ∑' n : ℕ, ∫ K : GW.Fock.Coordinates (n+1), (n+1 : ℝ) * freeSymbol P (n+1) K *
        ‖physicalSector (n+1) (graphEmbedding P x (n+1)) K‖ ^ 2 := by
  rw [movingEnergyAmbientField, LinearIsometryEquiv.norm_map, GW.Analysis.lp_norm_sq]
  exact tsum_congr (movingEnergySectorField_norm_sq P x)

end Froehlich
