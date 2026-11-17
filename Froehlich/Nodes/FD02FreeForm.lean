import Froehlich.Nodes.FD02

/-! FD02's literal free form in the fixed energy coordinates. Its diagonal
is the already verified physical free-energy integral, with no chosen ground energy. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

def freeFiberForm (P : GW.Space) : GW.Operators.AlgebraicForm (EnergySpace P) :=
  innerₛₗ ℂ - GW.Operators.embeddingForm (energyEmbedding P)

theorem freeFiberForm_apply (P : GW.Space) (w u : EnergySpace P) :
    freeFiberForm P w u = ⟪w,u⟫_ℂ - ⟪energyEmbedding P w,energyEmbedding P u⟫_ℂ := rfl

theorem freeFiberForm_hermitian (P : GW.Space) (w u : EnergySpace P) :
    freeFiberForm P w u = star (freeFiberForm P u w) := by
  simp only [freeFiberForm_apply, star_sub, Complex.star_def, inner_conj_symm]

theorem freeFiberForm_continuous (P : GW.Space) :
    Continuous (fun p : EnergySpace P × EnergySpace P => freeFiberForm P p.1 p.2) :=
  (continuous_fst.inner continuous_snd).sub
    (((energyEmbedding P).continuous.comp continuous_fst).inner
      ((energyEmbedding P).continuous.comp continuous_snd))

theorem freeFiberForm_shifted_norm (P : GW.Space) (u : EnergySpace P) :
    (freeFiberForm P u u).re + ‖energyEmbedding P u‖^2 = ‖u‖^2 := by
  rw [freeFiberForm_apply, Complex.sub_re]
  have hu := norm_sq_eq_re_inner (𝕜 := ℂ) u
  have hj := norm_sq_eq_re_inner (𝕜 := ℂ) (energyEmbedding P u)
  change ‖u‖^2 = (⟪u,u⟫_ℂ).re at hu
  change ‖energyEmbedding P u‖^2 = (⟪energyEmbedding P u,energyEmbedding P u⟫_ℂ).re at hj
  linarith

theorem freeFiberForm_physical_energy (P : GW.Space) (u : EnergySpace P) :
    (freeFiberForm P u u).re = freeEnergy P (energyEmbedding P u) := by
  have h := energyEmbedding_norm_identity P u
  have hq := freeFiberForm_shifted_norm P u
  linarith

/-- Actual free coercive data with shift one and both norm-equivalence constants one. -/
def freeFiberFormData (P : GW.Space) : GW.Operators.CoerciveFormData (EnergySpace P) GW.Fock.Carrier where
  embedding := energyEmbedding P
  embedding_injective := energyEmbedding_injective P
  embedding_dense := energyEmbedding_dense P
  form := freeFiberForm P
  hermitian := freeFiberForm_hermitian P
  continuous_form := freeFiberForm_continuous P
  shift := 1
  lower := 1
  upper := 1
  lower_pos := zero_lt_one
  lower_le_upper := le_rfl
  lower_bound u := by simpa only [one_mul] using (freeFiberForm_shifted_norm P u).symm.le
  upper_bound u := by simpa only [one_mul] using (freeFiberForm_shifted_norm P u).le

/-- A weak equation in the actual physical embedding, expressed by its adjoint;
no ambient-domain norm is substituted for the energy norm. -/
theorem freeFiberForm_weak_iff (P : GW.Space) (u : EnergySpace P) (f : GW.Fock.Carrier) :
    (∀ w, freeFiberForm P w u = ⟪energyEmbedding P w,f⟫_ℂ) ↔
      u = (energyEmbedding P).adjoint (f + energyEmbedding P u) := by
  constructor
  · intro h
    apply ext_inner_left ℂ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_right, inner_add_right]
    have hw := h w
    rw [freeFiberForm_apply] at hw
    linear_combination hw
  · intro h w
    have hw := congrArg (fun x : EnergySpace P => ⟪w,x⟫_ℂ) h
    rw [ContinuousLinearMap.adjoint_inner_right, inner_add_right] at hw
    rw [freeFiberForm_apply]
    linear_combination hw


theorem sectorEnergyEmbedding_pairing (P : GW.Space) (n : ℕ) (u v : GW.Fock.Sector n) :
    ⟪sectorEnergyEmbedding P n u,v⟫_ℂ = ⟪u,sectorEnergyEmbedding P n v⟫_ℂ := by
  rw [← (physicalSector n).inner_map_map (sectorEnergyEmbedding P n u) v,
    ← (physicalSector n).inner_map_map u (sectorEnergyEmbedding P n v), L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sectorEnergyEmbedding_weighted_ae P n u,
    sectorEnergyEmbedding_weighted_ae P n v] with k hu hv
  rw [← hv, ← hu, inner_smul_left, inner_smul_right, Complex.conj_ofReal]

theorem energyEmbedding_pairing (P : GW.Space) (x : EnergySpace P) (f : GW.Fock.Carrier) :
    ⟪energyEmbedding P x,f⟫_ℂ =
      ⟪x,(energyCoordinates P).symm (energyEmbedding P ((energyCoordinates P).symm f))⟫_ℂ := by
  change ⟪energyEmbedding P x,f⟫_ℂ =
    ⟪energyCoordinates P x,energyEmbedding P ((energyCoordinates P).symm f)⟫_ℂ
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [energyEmbedding_apply, energyEmbedding_apply, LinearIsometryEquiv.apply_symm_apply]
  exact sectorEnergyEmbedding_pairing P n _ _

theorem energyEmbedding_adjoint_apply (P : GW.Space) (f : GW.Fock.Carrier) :
    (energyEmbedding P).adjoint f =
      (energyCoordinates P).symm (energyEmbedding P ((energyCoordinates P).symm f)) := by
  apply ext_inner_left ℂ
  intro x
  exact ((energyEmbedding P).adjoint_inner_right x f).trans (energyEmbedding_pairing P x f)


/-- The reciprocal multiplier is the actual adjoint between the two named
Hilbert coordinate spaces. Multiplication by the weight recovers the source. -/
theorem energyEmbedding_adjoint_weighted_ae (P : GW.Space) (f : GW.Fock.Carrier) (n : ℕ) :
    (fun k => (energyWeight P n k : ℂ) •
      physicalSector n (energyCoordinates P ((energyEmbedding P).adjoint f) n) k)
        =ᵐ[GW.Fock.sectorMeasure n] physicalSector n (f n) := by
  rw [energyEmbedding_adjoint_apply, LinearIsometryEquiv.apply_symm_apply]
  have h := energyEmbedding_weighted_ae P ((energyCoordinates P).symm f) n
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h

/-- The weak free equation implies the full maximal multiplication equation,
with an actual square-summable output f, on every sector including vacuum. -/
theorem freeFiberForm_weak_implies_graph (P : GW.Space) (x : EnergySpace P) (f : GW.Fock.Carrier)
    (h : ∀ w, freeFiberForm P w x = ⟪energyEmbedding P w,f⟫_ℂ) :
    (energyEmbedding P x,f) ∈ (freeFiberOperator P).graph := by
  have hx := (freeFiberForm_weak_iff P x f).mp h
  apply (freeFiberOperator_graph_ae_iff P _ _).mpr
  intro n
  have h2 := energyEmbedding_adjoint_weighted_ae P (f + energyEmbedding P x) n
  rw [← hx] at h2
  have headd : physicalSector n ((f + energyEmbedding P x) n) =
      physicalSector n (f n) + physicalSector n (energyEmbedding P x n) := by
    change physicalSector n (f n + energyEmbedding P x n) = _
    exact map_add (physicalSector n) _ _
  rw [headd] at h2
  filter_upwards [energyEmbedding_weighted_ae P x n, h2,
    Lp.coeFn_add (physicalSector n (f n)) (physicalSector n (energyEmbedding P x n))] with k h1 h2 ha
  simp only [Pi.add_apply] at ha
  rw [ha] at h2
  simp only [smul_eq_mul] at h1 h2
  rw [← h1] at h2
  have hs : (energyWeight P n k : ℂ)^2 = 1 + (freeSymbol P n k : ℂ) := by
    calc
      _ = ((energyWeight P n k ^ 2 : ℝ) : ℂ) := (Complex.ofReal_pow _ _).symm
      _ = ((1 + freeSymbol P n k : ℝ) : ℂ) := congrArg Complex.ofReal (energyWeight_sq P n k)
      _ = _ := by rw [Complex.ofReal_add, Complex.ofReal_one]
  change (freeSymbol P n k : ℂ) * physicalSector n (energyEmbedding P x n) k = physicalSector n (f n) k
  linear_combination h2 - hs * physicalSector n (energyEmbedding P x n) k


theorem energyEmbedding_double_adjoint_ae (P : GW.Space) (f : GW.Fock.Carrier) (n : ℕ) :
    (fun k => (1 + (freeSymbol P n k : ℂ)) *
      physicalSector n (energyEmbedding P ((energyEmbedding P).adjoint f) n) k)
        =ᵐ[GW.Fock.sectorMeasure n] physicalSector n (f n) := by
  filter_upwards [energyEmbedding_weighted_ae P ((energyEmbedding P).adjoint f) n,
    energyEmbedding_adjoint_weighted_ae P f n] with k h1 h2
  simp only [smul_eq_mul] at h1 h2
  rw [← h1] at h2
  have hs : (energyWeight P n k : ℂ)^2 = 1 + (freeSymbol P n k : ℂ) := by
    calc
      _ = ((energyWeight P n k ^ 2 : ℝ) : ℂ) := (Complex.ofReal_pow _ _).symm
      _ = ((1 + freeSymbol P n k : ℝ) : ℂ) := congrArg Complex.ofReal (energyWeight_sq P n k)
      _ = _ := by rw [Complex.ofReal_add, Complex.ofReal_one]
  linear_combination h2 - hs * physicalSector n (energyEmbedding P ((energyEmbedding P).adjoint f) n) k

/-- Every vector in the maximal free graph has an actual energy-coordinate
lift. The construction uses two reciprocal weights, not a formal unbounded product. -/
theorem freeFiberOperator_graph_energyLift (P : GW.Space) (u f : GW.Fock.Carrier)
    (h : (u,f) ∈ (freeFiberOperator P).graph) :
    energyEmbedding P ((energyEmbedding P).adjoint (f + u)) = u := by
  have hg := (freeFiberOperator_graph_ae_iff P u f).mp h
  apply lp.ext
  funext n
  apply (physicalSector n).injective
  apply Lp.ext
  have h2 := energyEmbedding_double_adjoint_ae P (f + u) n
  have headd : physicalSector n ((f + u) n) = physicalSector n (f n) + physicalSector n (u n) := by
    change physicalSector n (f n + u n) = _
    exact map_add (physicalSector n) _ _
  rw [headd] at h2
  filter_upwards [h2, hg n, Lp.coeFn_add (physicalSector n (f n)) (physicalSector n (u n))]
    with k h2 hg ha
  simp only [Pi.add_apply] at ha
  rw [ha] at h2
  simp only [smul_eq_mul] at hg
  rw [← hg] at h2
  have hc : 1 + (freeSymbol P n k : ℂ) ≠ 0 := by
    have hr : (1 + freeSymbol P n k : ℝ) ≠ 0 := ne_of_gt (by linarith [freeSymbol_nonneg P n k])
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using Complex.ofReal_ne_zero.mpr hr
  apply mul_left_cancel₀ hc
  exact h2.trans (by ring)

/-- Exact two-sided identification of the physical weak graph and the maximal
multiplication graph; both quantifiers range over the full stated domains. -/
theorem freeFiberOperator_graph_weak_iff (P : GW.Space) (u f : GW.Fock.Carrier) :
    (u,f) ∈ (freeFiberOperator P).graph ↔
      ∃ x : EnergySpace P, energyEmbedding P x = u ∧
        ∀ w, freeFiberForm P w x = ⟪energyEmbedding P w,f⟫_ℂ := by
  constructor
  · intro h
    have hx := freeFiberOperator_graph_energyLift P u f h
    refine ⟨(energyEmbedding P).adjoint (f + u),hx,?_⟩
    apply (freeFiberForm_weak_iff P _ f).mpr
    rw [hx]
  · rintro ⟨x,hx,h⟩
    have hg := freeFiberForm_weak_implies_graph P x f h
    rwa [hx] at hg


/-- The associated free operator is exactly the maximal physical multiplier,
including equality of its entire domain and action. -/
theorem freeFiberOperator_eq_formOperator (P : GW.Space) :
    freeFiberOperator P = GW.Operators.formOperator (freeFiberFormData P) := by
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    rintro ⟨u,f⟩ h
    obtain ⟨x,hx,hweak⟩ := (freeFiberOperator_graph_weak_iff P u f).mp h
    obtain ⟨hm,hv⟩ := GW.Operators.formOperator_domain_of_equation (freeFiberFormData P) x f hweak
    exact (GW.Operators.formOperator (freeFiberFormData P)).mem_graph_iff.mpr
      ⟨⟨energyEmbedding P x,hm⟩,hx,hv⟩
  · apply LinearPMap.le_of_le_graph
    intro p hp
    obtain ⟨x,hx⟩ := (GW.Operators.formOperator (freeFiberFormData P)).mem_graph_iff'.mp hp
    rw [← hx]
    have hweak := GW.Operators.formOperator_form_identity (freeFiberFormData P) x
    have hemb := GW.Operators.operatorFormCoordinate_embedding (freeFiberFormData P) x
    change energyEmbedding P (GW.Operators.operatorFormCoordinate (freeFiberFormData P) x) = (x : GW.Fock.Carrier) at hemb
    have hg := freeFiberForm_weak_implies_graph P
      (GW.Operators.operatorFormCoordinate (freeFiberFormData P) x)
      (GW.Operators.formOperator (freeFiberFormData P) x) hweak
    rwa [hemb] at hg

theorem freeFiberOperator_selfadjoint (P : GW.Space) : GW.IsSelfAdjointOperator (freeFiberOperator P) := by
  rw [freeFiberOperator_eq_formOperator]
  exact GW.Operators.formOperator_selfadjoint (freeFiberFormData P)

end Froehlich
