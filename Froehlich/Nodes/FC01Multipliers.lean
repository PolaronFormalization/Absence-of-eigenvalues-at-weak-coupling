import Froehlich.Nodes.FC01

/-! Polynomial multiplication on the actual bounded momentum core. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

section BoundedSymbols
variable (m : ∀ n, GW.Fock.Coordinates n → ℝ)
  (hm : ∀ n, Measurable (m n)) (C : ℝ) (hC : 0 ≤ C)
  (hb : ∀ n k, |m n k| ≤ C)
  (hp : ∀ n (τ : Equiv.Perm (Fin n)) k, m n (fun i => k (τ i)) = m n k)

def boundedFockSector : ∀ n, GW.Fock.Sector n →L[ℂ] GW.Fock.Sector n
  | 0 => (m 0 0 : ℂ) • ContinuousLinearMap.id ℂ ℂ
  | n+1 => boundedSymmetricMultiplier (n+1) (fun k => (m (n+1) k : ℂ))
      (Complex.continuous_ofReal.measurable.comp (hm (n+1)))
      (fun k => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hb (n+1) k)
      (fun τ k => congrArg (fun x : ℝ => (x : ℂ)) (hp (n+1) τ k))

include hC in
theorem boundedFockSector_norm (n : ℕ) : ‖boundedFockSector m hm C hb hp n‖ ≤ C := by
  cases n with
  | zero =>
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro z
    change ‖(m 0 0 : ℂ) • z‖ ≤ C * ‖z‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hb 0 0) (norm_nonneg z)
  | succ n =>
    exact boundedSymmetricMultiplier_norm (n+1) (fun k => (m (n+1) k : ℂ))
      (Complex.continuous_ofReal.measurable.comp (hm (n+1))) hC
      (fun k => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hb (n+1) k)
      (fun τ k => congrArg (fun x : ℝ => (x : ℂ)) (hp (n+1) τ k))

def boundedFockAction : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  GW.Spaces.diagonalMap (boundedFockSector m hm C hb hp) hC
    (boundedFockSector_norm m hm C hC hb hp)

theorem boundedFockSector_ae (n : ℕ) (u : GW.Fock.Sector n) :
    (fun k => (m n k : ℂ) • physicalSector n u k) =ᵐ[GW.Fock.sectorMeasure n]
      physicalSector n (boundedFockSector m hm C hb hp n u) := by
  cases n with
  | zero =>
    filter_upwards [GW.Fock.vacuumAdapter_ae u,
      GW.Fock.vacuumAdapter_ae (boundedFockSector m hm C hb hp 0 u)] with k hu hv
    change (m 0 k : ℂ) • GW.Fock.vacuumAdapterIsometry u k =
      GW.Fock.vacuumAdapterIsometry (boundedFockSector m hm C hb hp 0 u) k
    rw [hu,hv,show k = 0 from Subsingleton.elim _ _]
    rfl
  | succ n =>
    exact boundedSymmetricMultiplier_ae (n+1) (fun k => (m (n+1) k : ℂ))
      (Complex.continuous_ofReal.measurable.comp (hm (n+1)))
      (C := C) (fun k => by
        simpa only [Complex.norm_real, Real.norm_eq_abs] using hb (n+1) k)
      (fun τ k => congrArg (fun x : ℝ => (x : ℂ)) (hp (n+1) τ k)) u

theorem boundedFockAction_ae (u : GW.Fock.Carrier) (n : ℕ) :
    (fun k => (m n k : ℂ) • physicalSector n (u n) k) =ᵐ[GW.Fock.sectorMeasure n]
      physicalSector n (boundedFockAction m hm C hC hb hp u n) := by
  exact boundedFockSector_ae m hm C hb hp n (u n)

theorem boundedFockAction_graph (u : GW.Fock.Carrier) :
    (u,boundedFockAction m hm C hC hb hp u) ∈ (fockRealMultiplier m).graph :=
  (fockRealMultiplier_graph_ae_iff _ _ _).mpr (boundedFockAction_ae m hm C hC hb hp u)

end BoundedSymbols

def coreCutoffSymbol (m : ∀ n, GW.Fock.Coordinates n → ℝ) (M R : ℕ)
    (n : ℕ) (k : GW.Fock.Coordinates n) : ℝ := by
  classical
  exact if n ≤ M then if k ∈ configurationBall n (R : ℝ) then m n k else 0 else 0

theorem coreCutoffSymbol_measurable (m : ∀ n, GW.Fock.Coordinates n → ℝ)
    (hm : ∀ n, Measurable (m n)) (M R n : ℕ) : Measurable (coreCutoffSymbol m M R n) := by
  classical
  unfold coreCutoffSymbol
  split_ifs with hn
  · exact Measurable.ite (configurationBall_measurable n (R : ℝ)) (hm n) measurable_const
  · exact measurable_const

theorem coreCutoffSymbol_permutation (m : ∀ n, GW.Fock.Coordinates n → ℝ)
    (hp : ∀ n (τ : Equiv.Perm (Fin n)) k, m n (fun i => k (τ i)) = m n k)
    (M R n : ℕ) (τ : Equiv.Perm (Fin n)) (k : GW.Fock.Coordinates n) :
    coreCutoffSymbol m M R n (fun i => k (τ i)) = coreCutoffSymbol m M R n k := by
  classical
  simp only [coreCutoffSymbol, configurationBall_permutation, hp]

theorem coreCutoffSymbol_bound (m : ∀ n, GW.Fock.Coordinates n → ℝ) (M R : ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n, n ≤ M → ∀ k ∈ configurationBall n (R : ℝ), |m n k| ≤ C) :
    ∀ n k, |coreCutoffSymbol m M R n k| ≤ C := by
  classical
  intro n k
  unfold coreCutoffSymbol
  split_ifs with hn hk
  · exact hb n hn k hk
  · simpa only [abs_zero] using hC
  · simpa only [abs_zero] using hC

theorem multiplier_graph_preserves_core (m : ∀ n, GW.Fock.Coordinates n → ℝ)
    (u : boundedMomentumCore) (v : GW.Fock.Carrier)
    (hg : ((u : GW.Fock.Carrier),v) ∈ (fockRealMultiplier m).graph) : v ∈ boundedMomentumCore := by
  obtain ⟨M,R,hM,hR,hfinite,hsupport⟩ := boundedMomentumCore_support u
  have ha := (fockRealMultiplier_graph_ae_iff m _ _).mp hg
  apply boundedMomentumCore_mem_of_support M R hM hR
  · intro n hn
    apply (physicalSector n).injective
    rw [map_zero]
    apply Lp.ext
    have hz : physicalSector n ((u : GW.Fock.Carrier) n) = 0 := by rw [hfinite n hn, map_zero]
    have h := ha n
    rw [hz] at h
    filter_upwards [h, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := GW.Fock.sectorMeasure n)] with k hk hzero
    simp only [Pi.zero_apply] at hzero
    rw [hzero, smul_zero] at hk
    simpa only [Pi.zero_apply] using hk.symm.trans hzero.symm
  · intro n
    filter_upwards [ha n, hsupport n] with k hk hs
    intro hout
    rw [← hk, hs hout, smul_zero]

theorem core_multiplier_graph_exists (m : ∀ n, GW.Fock.Coordinates n → ℝ)
    (hm : ∀ n, Measurable (m n))
    (hp : ∀ n (τ : Equiv.Perm (Fin n)) k, m n (fun i => k (τ i)) = m n k)
    (hloc : ∀ M R : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n, n ≤ M → ∀ k ∈ configurationBall n (R : ℝ), |m n k| ≤ C)
    (u : boundedMomentumCore) :
    ∃ v : GW.Fock.Carrier, v ∈ boundedMomentumCore ∧
      ((u : GW.Fock.Carrier),v) ∈ (fockRealMultiplier m).graph := by
  classical
  obtain ⟨M,R,hM,hR,hfinite,hsupport⟩ := boundedMomentumCore_support u
  obtain ⟨C,hC,hbound⟩ := hloc M R
  let mc := coreCutoffSymbol m M R
  have hmc := coreCutoffSymbol_measurable m hm M R
  have hbc := coreCutoffSymbol_bound m M R C hC hbound
  have hpc := coreCutoffSymbol_permutation m hp M R
  let v := boundedFockAction mc hmc C hC hbc hpc (u : GW.Fock.Carrier)
  have hg : ((u : GW.Fock.Carrier),v) ∈ (fockRealMultiplier m).graph := by
    apply (fockRealMultiplier_graph_ae_iff m _ _).mpr
    intro n
    have ha := boundedFockAction_ae mc hmc C hC hbc hpc (u : GW.Fock.Carrier) n
    by_cases hn : n ≤ M
    · filter_upwards [ha, hsupport n] with k hk hs
      rw [← hk]
      by_cases hball : k ∈ configurationBall n (R : ℝ)
      · simp only [mc, coreCutoffSymbol, if_pos hn, if_pos hball]
      · rw [hs hball, smul_zero, smul_zero]
    · have hz : physicalSector n ((u : GW.Fock.Carrier) n) = 0 := by
        rw [hfinite n (lt_of_not_ge hn), map_zero]
      rw [hz] at ha ⊢
      filter_upwards [ha, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := GW.Fock.sectorMeasure n)] with k hk hzero
      simp only [Pi.zero_apply] at hzero
      rw [hzero, smul_zero] at hk ⊢
      exact hk
  exact ⟨v,multiplier_graph_preserves_core m u v hg,hg⟩

end Froehlich
