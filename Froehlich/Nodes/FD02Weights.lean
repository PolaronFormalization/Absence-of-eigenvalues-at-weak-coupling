import Froehlich.Nodes.FD02

/-! FD02's arbitrary finite measurable symmetric weights, on the original
scalar-vacuum GW carrier. Complete physical domains use the retained product norm. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

def scalarWeightGraph (c : ℝ) (hc : 1 ≤ c) : GW.Spaces.WeightedGraph ℂ ℂ where
  domain := ⊤
  embedding := ((c⁻¹ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ ℂ
  embedding_injective := by
    intro x y h
    change ((c⁻¹ : ℝ) : ℂ) * x = ((c⁻¹ : ℝ) : ℂ) * y at h
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (inv_ne_zero
      (ne_of_gt (zero_lt_one.trans_le hc)))) h
  embedding_norm_le := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖((c⁻¹ : ℝ) : ℂ) • z‖ ≤ 1 * ‖z‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hc))]
    exact mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hc) (norm_nonneg z)
  embedding_dense := by
    apply Function.Surjective.denseRange
    intro z
    refine ⟨(c : ℂ) * z, ?_⟩
    change ((c⁻¹ : ℝ) : ℂ) * ((c : ℂ) * z) = z
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt (zero_lt_one.trans_le hc))]
    simp
  product :=
    { toFun := fun z => (c : ℂ) * (z : ℂ)
      map_add' := by intros; simp [mul_add]
      map_smul' := by intros; simp [smul_eq_mul]; ring }
  embedding_mem := fun _ => Submodule.mem_top
  product_embedding := by
    intro z
    change (c : ℂ) * (((c⁻¹ : ℝ) : ℂ) * z) = z
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt (zero_lt_one.trans_le hc))]
    simp
  embedding_product := by
    intro z
    change ((c⁻¹ : ℝ) : ℂ) * ((c : ℂ) * (z : ℂ)) = (z : ℂ)
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt (zero_lt_one.trans_le hc))]
    simp

section ArbitraryWeights
variable (w : ∀ n, GW.Fock.Coordinates n → ℝ)
  (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n k, 1 ≤ w n k)
  (hp : ∀ n (τ : Equiv.Perm (Fin n)) k, w n (fun i => k (τ i)) = w n k)

def fockWeightInvariant (n : ℕ) : GW.Spaces.WeightInvariant (GW.Fock.symmetricSector n) (hw n) (hw1 n) :=
  GW.Spaces.weightInvariant_of_functional (hw1 n)
    (symmetricWeight_functionalInvariant n (hw n) (hp n))

def fockWeightSectorGraph : ∀ n, GW.Spaces.WeightedGraph (GW.Fock.Sector n) (GW.Fock.Sector n)
  | 0 => scalarWeightGraph (w 0 0) (hw1 0 0)
  | n+1 => GW.Spaces.restrictedWeightedGraph (fockWeightInvariant w hw hw1 hp (n+1))

def fockWeightedGraph : GW.Spaces.WeightedGraph GW.Fock.Carrier GW.Fock.Carrier :=
  sumWeightedGraph (fockWeightSectorGraph w hw hw1 hp)

def fockWeightedCoordinates :
    GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp) ≃ₗᵢ[ℂ] GW.Fock.Carrier :=
  GW.Spaces.weightedDomainIsometry (fockWeightedGraph w hw hw1 hp)

example : CompleteSpace (GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp)) := inferInstance

theorem fockSectorWeightProduct_ae (n : ℕ) (u : (fockWeightSectorGraph w hw hw1 hp n).domain) :
    (fun k => (w n k : ℂ) • physicalSector n (u : GW.Fock.Sector n) k) =ᵐ[GW.Fock.sectorMeasure n]
      physicalSector n ((fockWeightSectorGraph w hw hw1 hp n).product u) := by
  cases n with
  | zero =>
    change (⊤ : Submodule ℂ ℂ) at u
    filter_upwards [GW.Fock.vacuumAdapter_ae (u : ℂ),
      GW.Fock.vacuumAdapter_ae ((fockWeightSectorGraph w hw hw1 hp 0).product u)] with k hu hv
    change (w 0 k : ℂ) * GW.Fock.vacuumAdapterIsometry (u : ℂ) k =
      GW.Fock.vacuumAdapterIsometry ((fockWeightSectorGraph w hw hw1 hp 0).product u) k
    rw [hu, hv, show k = 0 from Subsingleton.elim _ _]
    rfl
  | succ n =>
    exact GW.Analysis.realMultiplier_ae (w (n+1))
      (GW.Spaces.restrictedWeightInput (GW.Fock.symmetricSector (n+1)) (w (n+1)) u)

theorem fockSectorWeightProduct_norm_sq (n : ℕ) (u : (fockWeightSectorGraph w hw hw1 hp n).domain) :
    ‖(fockWeightSectorGraph w hw hw1 hp n).product u‖ ^ 2 =
      ∫ k, (w n k)^2 * ‖physicalSector n (u : GW.Fock.Sector n) k‖^2 ∂GW.Fock.sectorMeasure n := by
  rw [← (physicalSector n).norm_map ((fockWeightSectorGraph w hw hw1 hp n).product u),
    GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  apply integral_congr_ae
  filter_upwards [fockSectorWeightProduct_ae w hw hw1 hp n u] with k hk
  rw [← hk, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem fockSectorWeightProduct_graph_iff (n : ℕ) (u v : GW.Fock.Sector n) :
    (u,v) ∈ (sectorWeightPartial (fockWeightSectorGraph w hw hw1 hp) n).graph ↔
      (fun k => (w n k : ℂ) • physicalSector n u k) =ᵐ[GW.Fock.sectorMeasure n]
        physicalSector n v := by
  constructor
  · intro h
    obtain ⟨a, ha, hv⟩ := (sectorWeightPartial (fockWeightSectorGraph w hw hw1 hp) n).mem_graph_iff.mp h
    change (fockWeightSectorGraph w hw hw1 hp n).product a = v at hv
    simpa only [ha, hv] using fockSectorWeightProduct_ae w hw hw1 hp n a
  · intro h
    have hu : u ∈ (fockWeightSectorGraph w hw hw1 hp n).domain := by
      cases n with
      | zero =>
        change (show ℂ from u) ∈ (⊤ : Submodule ℂ ℂ)
        exact Submodule.mem_top
      | succ n => exact ⟨physicalSector (n+1) v, h⟩
    have hv : (fockWeightSectorGraph w hw hw1 hp n).product ⟨u,hu⟩ = v := by
      apply (physicalSector n).injective
      apply Lp.ext
      exact (fockSectorWeightProduct_ae w hw hw1 hp n ⟨u,hu⟩).symm.trans h
    exact (sectorWeightPartial (fockWeightSectorGraph w hw hw1 hp) n).mem_graph_iff.mpr
      ⟨⟨u,hu⟩,rfl,hv⟩

/-- Exact physical domain: the weighted products must be the coordinates of
one actual square-summable Fock vector. -/
theorem fockWeightedDomain_iff (u : GW.Fock.Carrier) :
    u ∈ (fockWeightedGraph w hw hw1 hp).domain ↔
      ∃ v : GW.Fock.Carrier, ∀ n,
        (fun k => (w n k : ℂ) • physicalSector n (u n) k) =ᵐ[GW.Fock.sectorMeasure n]
          physicalSector n (v n) := by
  rw [show (fockWeightedGraph w hw hw1 hp).domain =
    (GW.Fock.operatorSum GW.Fock.Sector (sectorWeightPartial (fockWeightSectorGraph w hw hw1 hp))).domain from rfl,
    GW.Fock.operatorSum_domain_iff]
  exact exists_congr (fun v => forall_congr' (fun n => fockSectorWeightProduct_graph_iff w hw hw1 hp n _ _))


theorem fockSectorWeightProduct_inner (n : ℕ)
    (u v : (fockWeightSectorGraph w hw hw1 hp n).domain) :
    ⟪(fockWeightSectorGraph w hw hw1 hp n).product u,
      (fockWeightSectorGraph w hw hw1 hp n).product v⟫_ℂ =
      ∫ k, ((w n k * w n k : ℝ) : ℂ) *
        ⟪physicalSector n (u : GW.Fock.Sector n) k,physicalSector n (v : GW.Fock.Sector n) k⟫_ℂ
          ∂GW.Fock.sectorMeasure n := by
  rw [← (physicalSector n).inner_map_map
    ((fockWeightSectorGraph w hw hw1 hp n).product u)
    ((fockWeightSectorGraph w hw hw1 hp n).product v), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fockSectorWeightProduct_ae w hw hw1 hp n u,
    fockSectorWeightProduct_ae w hw hw1 hp n v] with k hu hv
  rw [← hu, ← hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [Complex.ofReal_mul]
  ring


def weightedFockValue (u : GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp)) : GW.Fock.Carrier :=
  ((show (fockWeightedGraph w hw hw1 hp).domain from u) : GW.Fock.Carrier)

theorem fockWeighted_sector_norm_sq
    (u : GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp)) (n : ℕ) :
    ‖GW.Fock.operatorSum GW.Fock.Sector
      (sectorWeightPartial (fockWeightSectorGraph w hw hw1 hp))
        (show (fockWeightedGraph w hw hw1 hp).domain from u) n‖ ^ 2 =
      ∫ k, (w n k)^2 * ‖physicalSector n (weightedFockValue w hw hw1 hp u n) k‖^2
        ∂GW.Fock.sectorMeasure n := by
  let a : (fockWeightedGraph w hw hw1 hp).domain := u
  let s := GW.Fock.operatorSumInput GW.Fock.Sector
    (sectorWeightPartial (fockWeightSectorGraph w hw hw1 hp)) a n
  have he := GW.Fock.operatorSum_apply_component GW.Fock.Sector
    (sectorWeightPartial (fockWeightSectorGraph w hw hw1 hp)) a n
  change (fockWeightSectorGraph w hw hw1 hp n).product s =
    GW.Fock.operatorSum GW.Fock.Sector
      (sectorWeightPartial (fockWeightSectorGraph w hw hw1 hp)) a n at he
  change ‖GW.Fock.operatorSum GW.Fock.Sector
    (sectorWeightPartial (fockWeightSectorGraph w hw hw1 hp)) a n‖^2 = _
  rw [← he]
  exact fockSectorWeightProduct_norm_sq w hw hw1 hp n s

theorem fockWeighted_norm_sq
    (u : GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp)) :
    ‖u‖^2 = ∑' n, ∫ k, (w n k)^2 * ‖physicalSector n (weightedFockValue w hw hw1 hp u n) k‖^2
      ∂GW.Fock.sectorMeasure n := by
  have h := weightedSum_norm_sq (fockWeightSectorGraph w hw hw1 hp) u
  exact h.trans (tsum_congr (fockWeighted_sector_norm_sq w hw hw1 hp u))

theorem fockWeighted_integrals_summable
    (u : GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp)) :
    Summable (fun n => ∫ k, (w n k)^2 * ‖physicalSector n (weightedFockValue w hw hw1 hp u n) k‖^2
      ∂GW.Fock.sectorMeasure n) := by
  have h := (GW.Analysis.memℓp_two_iff_sq _).mp
    (GW.Fock.operatorSum GW.Fock.Sector
      (sectorWeightPartial (fockWeightSectorGraph w hw hw1 hp))
        (show (fockWeightedGraph w hw hw1 hp).domain from u)).property
  exact h.congr (fockWeighted_sector_norm_sq w hw hw1 hp u)


theorem fockWeighted_inner
    (u v : GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp)) :
    ⟪u,v⟫_ℂ = ∑' n, ∫ k, ((w n k * w n k : ℝ) : ℂ) *
      ⟪physicalSector n (weightedFockValue w hw hw1 hp u n) k,
        physicalSector n (weightedFockValue w hw hw1 hp v n) k⟫_ℂ ∂GW.Fock.sectorMeasure n := by
  let a : (fockWeightedGraph w hw hw1 hp).domain := u
  let b : (fockWeightedGraph w hw hw1 hp).domain := v
  let A := GW.Fock.operatorSum GW.Fock.Sector (sectorWeightPartial (fockWeightSectorGraph w hw hw1 hp))
  change ⟪A a,A b⟫_ℂ = _
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  let s := GW.Fock.operatorSumInput GW.Fock.Sector
    (sectorWeightPartial (fockWeightSectorGraph w hw hw1 hp)) a n
  let t := GW.Fock.operatorSumInput GW.Fock.Sector
    (sectorWeightPartial (fockWeightSectorGraph w hw hw1 hp)) b n
  have hu := GW.Fock.operatorSum_apply_component GW.Fock.Sector
    (sectorWeightPartial (fockWeightSectorGraph w hw hw1 hp)) a n
  have hv := GW.Fock.operatorSum_apply_component GW.Fock.Sector
    (sectorWeightPartial (fockWeightSectorGraph w hw hw1 hp)) b n
  change (fockWeightSectorGraph w hw hw1 hp n).product s = A a n at hu
  change (fockWeightSectorGraph w hw hw1 hp n).product t = A b n at hv
  rw [← hu, ← hv]
  exact fockSectorWeightProduct_inner w hw hw1 hp n s t


def fockWeightedInclusion :
    GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp) →L[ℂ] GW.Fock.Carrier :=
  (fockWeightedGraph w hw hw1 hp).embedding.comp
    (fockWeightedCoordinates w hw hw1 hp).toLinearIsometry.toContinuousLinearMap

theorem fockWeightedInclusion_apply
    (u : GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp)) :
    fockWeightedInclusion w hw hw1 hp u = weightedFockValue w hw hw1 hp u :=
  GW.Spaces.weightedDomain_embedding (fockWeightedGraph w hw hw1 hp) u

theorem fockWeightedInclusion_norm_le
    (u : GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp)) :
    ‖fockWeightedInclusion w hw hw1 hp u‖ ≤ ‖u‖ := by
  let G := fockWeightedGraph w hw hw1 hp
  have h := (G.embedding.le_opNorm ((fockWeightedCoordinates w hw hw1 hp) u)).trans
    (mul_le_mul_of_nonneg_right G.embedding_norm_le (norm_nonneg _))
  rw [one_mul, LinearIsometryEquiv.norm_map] at h
  exact h

theorem fockWeightedInclusion_injective : Function.Injective (fockWeightedInclusion w hw hw1 hp) := by
  intro u v h
  apply (fockWeightedCoordinates w hw hw1 hp).injective
  apply (fockWeightedGraph w hw hw1 hp).embedding_injective
  exact h

theorem fockWeightedInclusion_dense : DenseRange (fockWeightedInclusion w hw hw1 hp) := by
  let G := fockWeightedGraph w hw hw1 hp
  have hr : Set.range (fockWeightedInclusion w hw hw1 hp) = Set.range G.embedding := by
    ext u
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨fockWeightedCoordinates w hw hw1 hp x,rfl⟩
    · rintro ⟨x,rfl⟩
      refine ⟨(fockWeightedCoordinates w hw hw1 hp).symm x,?_⟩
      change G.embedding ((fockWeightedCoordinates w hw hw1 hp)
        ((fockWeightedCoordinates w hw hw1 hp).symm x)) = G.embedding x
      rw [LinearIsometryEquiv.apply_symm_apply]
  change Dense (Set.range (fockWeightedInclusion w hw hw1 hp))
  rw [hr]
  exact G.embedding_dense


end ArbitraryWeights
end Froehlich
