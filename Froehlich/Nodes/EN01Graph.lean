import Froehlich.Nodes.EN01

/-! EN01's free-operator graph coordinates use the actual multiplier graph weight.
The scalar vacuum and every symmetric sector retain their original GW carriers. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal

namespace Froehlich

theorem operatorGraphWeight_permutation (P : GW.Space) (n : ℕ)
    (τ : Equiv.Perm (Fin n)) (k : GW.Fock.Coordinates n) :
    operatorGraphWeight P n (fun i => k (τ i)) = operatorGraphWeight P n k := by
  simp only [operatorGraphWeight, freeSymbol_permutation]

theorem operatorGraphWeight_zero (P : GW.Space) (k : GW.Fock.Coordinates 0) :
    operatorGraphWeight P 0 k = Real.sqrt (1 + (‖P‖ ^ 2) ^ 2) := by
  simp [operatorGraphWeight, freeSymbol, totalMomentum]

/-- Exact agreement with the retained multiplier's graph-weight construction. -/
theorem operatorGraphWeight_eq_multiplierGraphWeight (P : GW.Space) (n : ℕ) :
    operatorGraphWeight P n = GW.Spaces.multiplierGraphWeight (freeSymbol P n) := rfl

theorem operatorGraphWeight_maximal_domain (P : GW.Space) (n : ℕ) :
    (GW.Analysis.realMultiplier (H := ℂ) (operatorGraphWeight P n)
      (GW.Fock.sectorMeasure n)).domain =
      (GW.Analysis.realMultiplier (H := ℂ) (freeSymbol P n)
        (GW.Fock.sectorMeasure n)).domain :=
  GW.Spaces.multiplierGraphWeight_domain (freeSymbol_measurable P n)

def operatorGraphWeightInvariant (P : GW.Space) (n : ℕ) :
    GW.Spaces.WeightInvariant (GW.Fock.symmetricSector n)
      (operatorGraphWeight_measurable P n) (operatorGraphWeight_ge_one P n) :=
  GW.Spaces.weightInvariant_of_functional (operatorGraphWeight_ge_one P n)
    (symmetricWeight_functionalInvariant n (operatorGraphWeight_measurable P n)
      (fun τ k => operatorGraphWeight_permutation P n τ k))

def sectorGraphEmbedding (P : GW.Space) : ∀ n, GW.Fock.Sector n →L[ℂ] GW.Fock.Sector n
  | 0 => (((Real.sqrt (1 + (‖P‖ ^ 2) ^ 2))⁻¹ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ ℂ
  | n+1 => GW.Spaces.restrictedReciprocal (operatorGraphWeightInvariant P (n+1))

theorem sectorGraphEmbedding_norm (P : GW.Space) (n : ℕ) :
    ‖sectorGraphEmbedding P n‖ ≤ 1 := by
  cases n with
  | zero =>
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖(((Real.sqrt (1 + (‖P‖ ^ 2) ^ 2))⁻¹ : ℝ) : ℂ) • z‖ ≤ 1 * ‖z‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
    apply inv_le_one_of_one_le₀
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (‖P‖ ^ 2)]
  | succ n =>
    exact GW.Spaces.restrictedWeightEmbedding_norm (operatorGraphWeightInvariant P (n+1))

def OperatorGraphSpace (_P : GW.Space) := GW.Fock.Carrier
instance (P : GW.Space) : NormedAddCommGroup (OperatorGraphSpace P) :=
  inferInstanceAs (NormedAddCommGroup GW.Fock.Carrier)
instance (P : GW.Space) : InnerProductSpace ℂ (OperatorGraphSpace P) :=
  inferInstanceAs (InnerProductSpace ℂ GW.Fock.Carrier)
instance (P : GW.Space) : CompleteSpace (OperatorGraphSpace P) :=
  inferInstanceAs (CompleteSpace GW.Fock.Carrier)

def graphCoordinates (P : GW.Space) : OperatorGraphSpace P ≃ₗᵢ[ℂ] GW.Fock.Carrier :=
  LinearIsometryEquiv.refl ℂ GW.Fock.Carrier

def graphEmbedding (P : GW.Space) : OperatorGraphSpace P →L[ℂ] GW.Fock.Carrier :=
  (GW.Spaces.diagonalMap (sectorGraphEmbedding P) zero_le_one
    (sectorGraphEmbedding_norm P)).comp (graphCoordinates P).toLinearIsometry.toContinuousLinearMap

theorem graphEmbedding_apply (P : GW.Space) (x : OperatorGraphSpace P) (n : ℕ) :
    graphEmbedding P x n = sectorGraphEmbedding P n (graphCoordinates P x n) := rfl

theorem graphEmbedding_opNorm (P : GW.Space) : ‖graphEmbedding P‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖GW.Spaces.diagonalLinear (sectorGraphEmbedding P) (sectorGraphEmbedding_norm P)
    (graphCoordinates P x)‖ ≤ 1 * ‖x‖
  have h := GW.Spaces.diagonal_norm_bound (sectorGraphEmbedding P) zero_le_one
    (sectorGraphEmbedding_norm P) (graphCoordinates P x)
  simpa only [LinearIsometryEquiv.norm_map] using h

section DirectSumWeightedGraph
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
  (G : ∀ n, GW.Spaces.WeightedGraph (E n) (E n))

/-- Assemble existing sector graph records using GW's existing diagonal and partial sum APIs. -/
def sectorWeightPartial (n : ℕ) : E n →ₗ.[ℂ] E n where
  domain := (G n).domain
  toFun := (G n).product

def sumGraphEmbedding : lp E 2 →L[ℂ] lp E 2 :=
  GW.Spaces.diagonalMap (fun n => (G n).embedding) zero_le_one
    (fun n => (G n).embedding_norm_le)

theorem sectorWeight_embedding (n : ℕ) (x : E n) :
    sectorWeightPartial G n ⟨(G n).embedding x, (G n).embedding_mem x⟩ = x :=
  (G n).product_embedding x

theorem sumGraphEmbedding_injective : Function.Injective (sumGraphEmbedding G) := by
  intro x y h
  apply lp.ext
  funext n
  apply (G n).embedding_injective
  exact congrArg (fun z : lp E 2 => z n) h

theorem sumGraphEmbedding_range : Set.range (sumGraphEmbedding G) =
    ((GW.Fock.operatorSum E (sectorWeightPartial G)).domain : Set (lp E 2)) := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    apply (GW.Fock.operatorSum E (sectorWeightPartial G)).mem_domain_of_mem_graph (y := x)
    rw [GW.Fock.operatorSum_graph_iff]
    intro n
    have h := (sectorWeightPartial G n).mem_graph
      ⟨(G n).embedding (x n), (G n).embedding_mem (x n)⟩
    rw [sectorWeight_embedding] at h
    exact h
  · intro hu
    refine ⟨GW.Fock.operatorSum E (sectorWeightPartial G) ⟨u, hu⟩, ?_⟩
    apply lp.ext
    funext n
    change (G n).embedding (GW.Fock.operatorSum E (sectorWeightPartial G) ⟨u,hu⟩ n) = u n
    rw [← GW.Fock.operatorSum_apply_component]
    exact (G n).embedding_product _

theorem sumGraphEmbedding_dense : DenseRange (sumGraphEmbedding G) := by
  change Dense (Set.range (sumGraphEmbedding G))
  rw [sumGraphEmbedding_range]
  apply GW.Fock.operatorSum_dense
  intro n
  have hr : Set.range (G n).embedding = ((G n).domain : Set (E n)) := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩; exact (G n).embedding_mem x
    · intro hu; exact ⟨(G n).product ⟨u, hu⟩, (G n).embedding_product _⟩
  have hd := (G n).embedding_dense
  change Dense (Set.range (G n).embedding) at hd
  rw [hr] at hd
  exact hd
end DirectSumWeightedGraph

def vacuumGraphWeight (P : GW.Space) : ℝ := Real.sqrt (1 + (‖P‖ ^ 2) ^ 2)

theorem vacuumGraphWeight_ne_zero (P : GW.Space) : vacuumGraphWeight P ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (by positivity))

def vacuumGraphRecord (P : GW.Space) : GW.Spaces.WeightedGraph ℂ ℂ where
  domain := ⊤
  embedding := sectorGraphEmbedding P 0
  embedding_injective := by
    change Function.Injective (fun z : ℂ => (((vacuumGraphWeight P)⁻¹ : ℝ) : ℂ) * z)
    intro x y h
    exact mul_left_cancel₀ (by exact_mod_cast inv_ne_zero (vacuumGraphWeight_ne_zero P)) h
  embedding_norm_le := sectorGraphEmbedding_norm P 0
  embedding_dense := by
    apply Function.Surjective.denseRange
    intro z
    refine ⟨(vacuumGraphWeight P : ℂ) * z, ?_⟩
    change (((vacuumGraphWeight P)⁻¹ : ℝ) : ℂ) * ((vacuumGraphWeight P : ℂ) * z) = z
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (vacuumGraphWeight_ne_zero P)]
    simp
  product :=
    { toFun := fun z => (vacuumGraphWeight P : ℂ) * (z : ℂ)
      map_add' := by intros; simp [mul_add]
      map_smul' := by intros; simp [smul_eq_mul]; ring }
  embedding_mem := fun _ => Submodule.mem_top
  product_embedding := by
    intro z
    change (vacuumGraphWeight P : ℂ) * ((((vacuumGraphWeight P)⁻¹ : ℝ) : ℂ) * z) = z
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (vacuumGraphWeight_ne_zero P)]
    simp
  embedding_product := by
    intro z
    change (((vacuumGraphWeight P)⁻¹ : ℝ) : ℂ) *
      ((vacuumGraphWeight P : ℂ) * (z : ℂ)) = (z : ℂ)
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (vacuumGraphWeight_ne_zero P)]
    simp

def sectorGraphRecord (P : GW.Space) : ∀ n,
    GW.Spaces.WeightedGraph (GW.Fock.Sector n) (GW.Fock.Sector n)
  | 0 => vacuumGraphRecord P
  | n+1 => GW.Spaces.restrictedWeightedGraph (operatorGraphWeightInvariant P (n+1))

def graphWeightOperator (P : GW.Space) : GW.Fock.Carrier →ₗ.[ℂ] GW.Fock.Carrier :=
  GW.Fock.operatorSum GW.Fock.Sector (sectorWeightPartial (sectorGraphRecord P))

theorem graphEmbedding_eq_sum (P : GW.Space) (x : OperatorGraphSpace P) :
    graphEmbedding P x = sumGraphEmbedding (sectorGraphRecord P) (graphCoordinates P x) := by
  apply lp.ext
  funext n
  cases n <;> rfl

theorem graphEmbedding_injective (P : GW.Space) : Function.Injective (graphEmbedding P) := by
  intro x y h
  apply (graphCoordinates P).injective
  apply sumGraphEmbedding_injective (sectorGraphRecord P)
  simpa only [← graphEmbedding_eq_sum] using h

theorem graphEmbedding_range (P : GW.Space) : Set.range (graphEmbedding P) =
    ((graphWeightOperator P).domain : Set GW.Fock.Carrier) := by
  have hr : Set.range (graphEmbedding P) = Set.range (sumGraphEmbedding (sectorGraphRecord P)) := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨graphCoordinates P x, (graphEmbedding_eq_sum P x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨(graphCoordinates P).symm x, by rw [graphEmbedding_eq_sum, LinearIsometryEquiv.apply_symm_apply]⟩
  rw [hr]
  exact sumGraphEmbedding_range (sectorGraphRecord P)

theorem graphEmbedding_dense (P : GW.Space) : DenseRange (graphEmbedding P) := by
  change Dense (Set.range (graphEmbedding P))
  rw [graphEmbedding_range]
  have h := sumGraphEmbedding_dense (sectorGraphRecord P)
  change Dense (Set.range (sumGraphEmbedding (sectorGraphRecord P))) at h
  rw [sumGraphEmbedding_range] at h
  exact h

def normalizedFreeFunction (t : ℝ) : ℂ := (t / Real.sqrt (1+t^2) : ℝ)

theorem normalizedFreeFunction_measurable : Measurable normalizedFreeFunction := by
  unfold normalizedFreeFunction
  fun_prop

theorem normalizedFreeFunction_bound (t : ℝ) : ‖normalizedFreeFunction t‖ ≤ 1 := by
  have hr : 0 < Real.sqrt (1+t^2) := Real.sqrt_pos.mpr (by positivity)
  rw [normalizedFreeFunction, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_of_pos hr]
  exact (div_le_one hr).mpr (Real.abs_le_sqrt (by nlinarith))

def sectorGraphAction (P : GW.Space) : ∀ n, GW.Fock.Sector n →L[ℂ] GW.Fock.Sector n
  | 0 => normalizedFreeFunction (‖P‖^2) • ContinuousLinearMap.id ℂ ℂ
  | n+1 =>
    ((GW.Analysis.boundedMultiplier (normalizedFreeFunction ∘ freeSymbol P (n+1))
      (normalizedFreeFunction_measurable.comp (freeSymbol_measurable P (n+1)))
      (Eventually.of_forall (fun k => normalizedFreeFunction_bound (freeSymbol P (n+1) k)))).comp
        (GW.Fock.symmetricSector (n+1)).toSubmodule.subtypeL).codRestrict
      (GW.Fock.symmetricSector (n+1)).toSubmodule
      (fun u => symmetricWeight_functionalInvariant (n+1) (freeSymbol_measurable P (n+1))
        (fun τ k => freeSymbol_permutation P (n+1) τ k)
        normalizedFreeFunction normalizedFreeFunction_measurable normalizedFreeFunction_bound u)

theorem sectorGraphAction_norm (P : GW.Space) (n : ℕ) : ‖sectorGraphAction P n‖ ≤ 1 := by
  cases n with
  | zero =>
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖normalizedFreeFunction (‖P‖^2) • z‖ ≤ 1 * ‖z‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (normalizedFreeFunction_bound _) (norm_nonneg _)
  | succ n =>
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    change ‖GW.Analysis.boundedMultiplier (normalizedFreeFunction ∘ freeSymbol P (n+1))
      (normalizedFreeFunction_measurable.comp (freeSymbol_measurable P (n+1)))
      (Eventually.of_forall (fun k => normalizedFreeFunction_bound (freeSymbol P (n+1) k)))
      (GW.Fock.sectorInclusion n u)‖ ≤ 1 * ‖GW.Fock.sectorInclusion n u‖
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [GW.Analysis.boundedMultiplier_ae
      (normalizedFreeFunction ∘ freeSymbol P (n+1))
      (normalizedFreeFunction_measurable.comp (freeSymbol_measurable P (n+1)))
      (Eventually.of_forall (fun k => normalizedFreeFunction_bound (freeSymbol P (n+1) k)))
      (GW.Fock.sectorInclusion n u)] with k hk
    rw [← hk, norm_smul]
    exact mul_le_mul_of_nonneg_right (normalizedFreeFunction_bound _) (norm_nonneg _)

/-- The genuine free multiplier applied to a graph-coordinate vector. -/
def freeActionOnGraph (P : GW.Space) : OperatorGraphSpace P →L[ℂ] GW.Fock.Carrier :=
  (GW.Spaces.diagonalMap (sectorGraphAction P) zero_le_one (sectorGraphAction_norm P)).comp
    (graphCoordinates P).toLinearIsometry.toContinuousLinearMap

theorem graphEmbedding_reciprocal_ae (P : GW.Space) (x : OperatorGraphSpace P) (n : ℕ) :
    (fun k => (((operatorGraphWeight P n k)⁻¹ : ℝ) : ℂ) •
      physicalSector n (graphCoordinates P x n) k) =ᵐ[GW.Fock.sectorMeasure n]
        physicalSector n (graphEmbedding P x n) := by
  cases n with
  | zero =>
    filter_upwards [GW.Fock.vacuumAdapter_ae (graphCoordinates P x 0),
      GW.Fock.vacuumAdapter_ae (graphEmbedding P x 0)] with k hx hu
    change (((operatorGraphWeight P 0 k)⁻¹ : ℝ) : ℂ) •
      GW.Fock.vacuumAdapterIsometry (graphCoordinates P x 0) k =
        GW.Fock.vacuumAdapterIsometry (graphEmbedding P x 0) k
    rw [hx, hu, operatorGraphWeight_zero]
    rfl
  | succ n =>
    exact GW.Analysis.boundedMultiplier_ae
      (fun k => (((operatorGraphWeight P (n+1) k)⁻¹ : ℝ) : ℂ))
      (Complex.continuous_ofReal.measurable.comp (operatorGraphWeight_measurable P (n+1)).inv)
      (GW.Spaces.WeightedL2.reciprocal_bound (operatorGraphWeight_ge_one P (n+1)))
      (physicalSector (n+1) (graphCoordinates P x (n+1)))

theorem graphEmbedding_weighted_ae (P : GW.Space) (x : OperatorGraphSpace P) (n : ℕ) :
    (fun k => (operatorGraphWeight P n k : ℂ) •
      physicalSector n (graphEmbedding P x n) k) =ᵐ[GW.Fock.sectorMeasure n]
        physicalSector n (graphCoordinates P x n) := by
  filter_upwards [graphEmbedding_reciprocal_ae P x n] with k hk
  rw [← hk, smul_smul, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (ne_of_gt (zero_lt_one.trans_le (operatorGraphWeight_ge_one P n k)))]
  simp

theorem freeActionOnGraph_ae (P : GW.Space) (x : OperatorGraphSpace P) (n : ℕ) :
    (fun k => (freeSymbol P n k : ℂ) • physicalSector n (graphEmbedding P x n) k) =ᵐ[GW.Fock.sectorMeasure n]
      physicalSector n (freeActionOnGraph P x n) := by
  cases n with
  | zero =>
    filter_upwards [GW.Fock.vacuumAdapter_ae (graphEmbedding P x 0),
      GW.Fock.vacuumAdapter_ae (freeActionOnGraph P x 0)] with k hu hv
    change (freeSymbol P 0 k : ℂ) * GW.Fock.vacuumAdapterIsometry (graphEmbedding P x 0) k =
      GW.Fock.vacuumAdapterIsometry (freeActionOnGraph P x 0) k
    rw [hu, hv]
    let z : ℂ := graphCoordinates P x 0
    change (freeSymbol P 0 k : ℂ) *
      ((((Real.sqrt (1+(‖P‖^2)^2))⁻¹ : ℝ) : ℂ) * z) =
        normalizedFreeFunction (‖P‖^2) * z
    simp [freeSymbol, totalMomentum, normalizedFreeFunction, div_eq_mul_inv, mul_assoc]
  | succ n =>
    have ha := GW.Analysis.boundedMultiplier_ae
      (normalizedFreeFunction ∘ freeSymbol P (n+1))
      (normalizedFreeFunction_measurable.comp (freeSymbol_measurable P (n+1)))
      (Eventually.of_forall (fun k => normalizedFreeFunction_bound (freeSymbol P (n+1) k)))
      (physicalSector (n+1) (graphCoordinates P x (n+1)))
    filter_upwards [graphEmbedding_reciprocal_ae P x (n+1), ha] with k hu hv
    change _ = GW.Analysis.boundedMultiplier
      (normalizedFreeFunction ∘ freeSymbol P (n+1))
      (normalizedFreeFunction_measurable.comp (freeSymbol_measurable P (n+1)))
      (Eventually.of_forall (fun k => normalizedFreeFunction_bound (freeSymbol P (n+1) k)))
      (physicalSector (n+1) (graphCoordinates P x (n+1))) k
    rw [← hu, ← hv, smul_smul]
    congr 1
    simp [normalizedFreeFunction, operatorGraphWeight, div_eq_mul_inv]

def freeGraphSectorInput (P : GW.Space) (x : OperatorGraphSpace P) (n : ℕ) :
    (GW.Analysis.realMultiplier (H := ℂ) (freeSymbol P n) (GW.Fock.sectorMeasure n)).domain :=
  ⟨physicalSector n (graphEmbedding P x n),
    ⟨physicalSector n (freeActionOnGraph P x n), freeActionOnGraph_ae P x n⟩⟩

theorem graph_norm_sector (P : GW.Space) (x : OperatorGraphSpace P) (n : ℕ) :
    ‖graphCoordinates P x n‖ ^ 2 =
      ‖graphEmbedding P x n‖ ^ 2 + ‖freeActionOnGraph P x n‖ ^ 2 := by
  let u := freeGraphSectorInput P x n
  let q := GW.Spaces.multiplierGraphInput (freeSymbol_measurable P n) u
  have h := GW.Spaces.multiplierGraphWeight_norm_sq (freeSymbol_measurable P n) u
  have hf : GW.Analysis.realMultiplier (freeSymbol P n) (GW.Fock.sectorMeasure n) u =
      physicalSector n (freeActionOnGraph P x n) := by
    apply Lp.ext
    exact (GW.Analysis.realMultiplier_ae (freeSymbol P n) u).symm.trans (freeActionOnGraph_ae P x n)
  have hq : GW.Analysis.realMultiplier (operatorGraphWeight P n) (GW.Fock.sectorMeasure n) q =
      physicalSector n (graphCoordinates P x n) := by
    apply Lp.ext
    exact (GW.Analysis.realMultiplier_ae (operatorGraphWeight P n) q).symm.trans
      (graphEmbedding_weighted_ae P x n)
  change ‖GW.Analysis.realMultiplier (operatorGraphWeight P n) (GW.Fock.sectorMeasure n) q‖ ^ 2 =
    ‖physicalSector n (graphEmbedding P x n)‖ ^ 2 +
      ‖GW.Analysis.realMultiplier (freeSymbol P n) (GW.Fock.sectorMeasure n) u‖ ^ 2 at h
  rw [hq, hf] at h
  simpa only [LinearIsometry.norm_map] using h

theorem graph_norm_identity (P : GW.Space) (x : OperatorGraphSpace P) :
    ‖x‖ ^ 2 = ‖graphEmbedding P x‖ ^ 2 + ‖freeActionOnGraph P x‖ ^ 2 := by
  have hu := (GW.Analysis.memℓp_two_iff_sq _).mp (graphEmbedding P x).property
  have hv := (GW.Analysis.memℓp_two_iff_sq _).mp (freeActionOnGraph P x).property
  rw [← (graphCoordinates P).norm_map x, GW.Fock.carrier_norm_sq,
    GW.Fock.carrier_norm_sq, GW.Fock.carrier_norm_sq]
  simp_rw [graph_norm_sector]
  exact Summable.tsum_add hu hv

theorem sectorGraphAction_ae (P : GW.Space) (n : ℕ) (x : GW.Fock.Sector n) :
    (fun k => (freeSymbol P n k : ℂ) • physicalSector n (sectorGraphEmbedding P n x) k) =ᵐ[GW.Fock.sectorMeasure n]
      physicalSector n (sectorGraphAction P n x) := by
  have h := freeActionOnGraph_ae P ((graphCoordinates P).symm (lp.single 2 n x)) n
  change (fun k => (freeSymbol P n k : ℂ) •
    physicalSector n (sectorGraphEmbedding P n ((lp.single 2 n x) n)) k) =ᵐ[GW.Fock.sectorMeasure n]
      physicalSector n (sectorGraphAction P n ((lp.single 2 n x) n)) at h
  simpa only [lp.single_apply_self] using h

theorem sectorGraph_norm_identity (P : GW.Space) (n : ℕ) (x : GW.Fock.Sector n) :
    ‖x‖ ^ 2 = ‖sectorGraphEmbedding P n x‖ ^ 2 + ‖sectorGraphAction P n x‖ ^ 2 := by
  have h := graph_norm_sector P ((graphCoordinates P).symm (lp.single 2 n x)) n
  change ‖(lp.single 2 n x) n‖ ^ 2 =
    ‖sectorGraphEmbedding P n ((lp.single 2 n x) n)‖ ^ 2 +
      ‖sectorGraphAction P n ((lp.single 2 n x) n)‖ ^ 2 at h
  simpa only [lp.single_apply_self] using h

theorem graphEmbedding_mem_domain (P : GW.Space) (x : OperatorGraphSpace P) :
    graphEmbedding P x ∈ (graphWeightOperator P).domain := by
  exact (graphEmbedding_range P).subset ⟨x, rfl⟩

theorem graphEmbedding_product (P : GW.Space) (u : (graphWeightOperator P).domain) :
    graphEmbedding P ((graphCoordinates P).symm (graphWeightOperator P u)) = (u : GW.Fock.Carrier) := by
  rw [graphEmbedding_eq_sum, LinearIsometryEquiv.apply_symm_apply]
  apply lp.ext
  funext n
  change (sectorGraphRecord P n).embedding
    (GW.Fock.operatorSum GW.Fock.Sector (sectorWeightPartial (sectorGraphRecord P)) u n) =
      (u : GW.Fock.Carrier) n
  let u₀ : (GW.Fock.operatorSum GW.Fock.Sector
      (sectorWeightPartial (sectorGraphRecord P))).domain := ⟨(u : GW.Fock.Carrier), u.property⟩
  have he := GW.Fock.operatorSum_apply_component GW.Fock.Sector
    (sectorWeightPartial (sectorGraphRecord P)) u₀ n
  have hp := (sectorGraphRecord P n).embedding_product
    (GW.Fock.operatorSumInput GW.Fock.Sector (sectorWeightPartial (sectorGraphRecord P)) u₀ n)
  exact (congrArg (sectorGraphRecord P n).embedding he).symm.trans hp

/-- The free fiber multiplier on its actual maximal graph domain. -/
def freeFiberOperator (P : GW.Space) : GW.Fock.Carrier →ₗ.[ℂ] GW.Fock.Carrier where
  domain := (graphWeightOperator P).domain
  toFun := (freeActionOnGraph P).toLinearMap.comp
    ((graphCoordinates P).symm.toLinearMap.comp (graphWeightOperator P).toFun)

theorem freeFiberOperator_ae (P : GW.Space) (u : (freeFiberOperator P).domain) (n : ℕ) :
    (fun k => (freeSymbol P n k : ℂ) • physicalSector n ((u : GW.Fock.Carrier) n) k) =ᵐ[GW.Fock.sectorMeasure n]
      physicalSector n (freeFiberOperator P u n) := by
  let u₀ : (graphWeightOperator P).domain := ⟨(u : GW.Fock.Carrier), u.property⟩
  have h := freeActionOnGraph_ae P ((graphCoordinates P).symm (graphWeightOperator P u₀)) n
  rw [graphEmbedding_product P u₀] at h
  exact h

theorem freeFiberOperator_graph_norm (P : GW.Space) (u : (freeFiberOperator P).domain) :
    ‖graphWeightOperator P u‖ ^ 2 = ‖(u : GW.Fock.Carrier)‖ ^ 2 + ‖freeFiberOperator P u‖ ^ 2 := by
  let u₀ : (graphWeightOperator P).domain := ⟨(u : GW.Fock.Carrier), u.property⟩
  have h := graph_norm_identity P ((graphCoordinates P).symm (graphWeightOperator P u₀))
  rw [graphEmbedding_product P u₀, LinearIsometryEquiv.norm_map] at h
  exact h

theorem sectorGraphRecord_embedding (P : GW.Space) (n : ℕ) :
    (sectorGraphRecord P n).embedding = sectorGraphEmbedding P n := by
  cases n <;> rfl

def maximalFreeSectorInput (P : GW.Space) (u v : GW.Fock.Carrier)
    (h : ∀ n, (fun k => (freeSymbol P n k : ℂ) • physicalSector n (u n) k) =ᵐ[GW.Fock.sectorMeasure n]
      physicalSector n (v n)) (n : ℕ) : (sectorWeightPartial (sectorGraphRecord P) n).domain := by
  cases n with
  | zero =>
    change (⊤ : Submodule ℂ ℂ)
    exact ⟨(show ℂ from u 0), Submodule.mem_top⟩
  | succ n =>
    change GW.Spaces.restrictedWeightDomain (GW.Fock.symmetricSector (n+1))
      (operatorGraphWeight P (n+1))
    refine ⟨u (n+1), ?_⟩
    change physicalSector (n+1) (u (n+1)) ∈
      (GW.Analysis.realMultiplier (H := ℂ) (operatorGraphWeight P (n+1))
        (GW.Fock.sectorMeasure (n+1))).domain
    rw [operatorGraphWeight_maximal_domain]
    exact ⟨physicalSector (n+1) (v (n+1)), h (n+1)⟩

theorem maximalFreeSectorInput_coe (P : GW.Space) (u v : GW.Fock.Carrier)
    (h : ∀ n, (fun k => (freeSymbol P n k : ℂ) • physicalSector n (u n) k) =ᵐ[GW.Fock.sectorMeasure n]
      physicalSector n (v n)) (n : ℕ) :
    (maximalFreeSectorInput P u v h n : GW.Fock.Sector n) = u n := by
  cases n <;> rfl

theorem maximalFreeSectorInput_norm (P : GW.Space) (u v : GW.Fock.Carrier)
    (h : ∀ n, (fun k => (freeSymbol P n k : ℂ) • physicalSector n (u n) k) =ᵐ[GW.Fock.sectorMeasure n]
      physicalSector n (v n)) (n : ℕ) :
    ‖(sectorGraphRecord P n).product (maximalFreeSectorInput P u v h n)‖ ^ 2 =
      ‖u n‖ ^ 2 + ‖v n‖ ^ 2 := by
  have he := (sectorGraphRecord P n).embedding_product (maximalFreeSectorInput P u v h n)
  rw [sectorGraphRecord_embedding, maximalFreeSectorInput_coe] at he
  have ha : sectorGraphAction P n
      ((sectorGraphRecord P n).product (maximalFreeSectorInput P u v h n)) = v n := by
    apply (physicalSector n).injective
    apply Lp.ext
    have hq := sectorGraphAction_ae P n
      ((sectorGraphRecord P n).product (maximalFreeSectorInput P u v h n))
    rw [he] at hq
    exact hq.symm.trans (h n)
  have hn := sectorGraph_norm_identity P n
    ((sectorGraphRecord P n).product (maximalFreeSectorInput P u v h n))
  rw [he, ha] at hn
  exact hn

/-- The domain is exactly the maximal free multiplier domain with a square-summable
canonical output. No finite-particle or support restriction is imposed. -/
theorem freeFiberOperator_domain_iff (P : GW.Space) (u : GW.Fock.Carrier) :
    u ∈ (freeFiberOperator P).domain ↔ ∃ v : GW.Fock.Carrier,
      ∀ n, (fun k => (freeSymbol P n k : ℂ) • physicalSector n (u n) k) =ᵐ[GW.Fock.sectorMeasure n]
        physicalSector n (v n) := by
  constructor
  · intro hu
    exact ⟨freeFiberOperator P ⟨u,hu⟩, freeFiberOperator_ae P ⟨u,hu⟩⟩
  · rintro ⟨v, h⟩
    have hs : Summable (fun n =>
        ‖(sectorGraphRecord P n).product (maximalFreeSectorInput P u v h n)‖ ^ 2) := by
      simp_rw [maximalFreeSectorInput_norm]
      exact ((GW.Analysis.memℓp_two_iff_sq _).mp u.property).add
        ((GW.Analysis.memℓp_two_iff_sq _).mp v.property)
    let z : GW.Fock.Carrier := GW.Analysis.squareSumVector
      (fun n => (sectorGraphRecord P n).product (maximalFreeSectorInput P u v h n)) hs
    change u ∈ (GW.Fock.operatorSum GW.Fock.Sector
      (sectorWeightPartial (sectorGraphRecord P))).domain
    apply (GW.Fock.operatorSum GW.Fock.Sector (sectorWeightPartial (sectorGraphRecord P))).mem_domain_of_mem_graph (y := z)
    rw [GW.Fock.operatorSum_graph_iff]
    intro n
    change (u n, (sectorGraphRecord P n).product (maximalFreeSectorInput P u v h n)) ∈
      (sectorWeightPartial (sectorGraphRecord P) n).graph
    have hm := (sectorWeightPartial (sectorGraphRecord P) n).mem_graph
      (maximalFreeSectorInput P u v h n)
    change ((maximalFreeSectorInput P u v h n : GW.Fock.Sector n),
      (sectorGraphRecord P n).product (maximalFreeSectorInput P u v h n)) ∈
        (sectorWeightPartial (sectorGraphRecord P) n).graph at hm
    rw [maximalFreeSectorInput_coe] at hm
    exact hm

theorem freeFiberOperator_domain_action_iff (P : GW.Space) (u v : GW.Fock.Carrier) :
    (∃ hu : u ∈ (freeFiberOperator P).domain, freeFiberOperator P ⟨u,hu⟩ = v) ↔
      ∀ n, (fun k => (freeSymbol P n k : ℂ) • physicalSector n (u n) k) =ᵐ[GW.Fock.sectorMeasure n]
        physicalSector n (v n) := by
  constructor
  · rintro ⟨hu, rfl⟩
    exact freeFiberOperator_ae P ⟨u,hu⟩
  · intro h
    have hu := (freeFiberOperator_domain_iff P u).mpr ⟨v,h⟩
    refine ⟨hu, ?_⟩
    apply lp.ext
    funext n
    apply (physicalSector n).injective
    apply Lp.ext
    exact (freeFiberOperator_ae P ⟨u,hu⟩ n).symm.trans (h n)

end Froehlich
