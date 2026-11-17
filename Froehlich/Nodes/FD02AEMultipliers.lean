import Froehlich.Nodes.FD02Multipliers

/-! User-approved FD02 erratum: bosonic multiplier density needs only
almost-everywhere permutation invariance. The original maximal graph is kept. -/
noncomputable section
open MeasureTheory Filter
namespace Froehlich

def permutationGoodSet (n : ℕ) (a : GW.Fock.Coordinates n → ℝ) : Set (GW.Fock.Coordinates n) :=
  {k | ∀ τ : Equiv.Perm (Fin n), a (fun i => k (τ i)) = a k}

theorem permutationGoodSet_stable (n : ℕ) (a : GW.Fock.Coordinates n → ℝ)
    (σ : Equiv.Perm (Fin n)) (k : GW.Fock.Coordinates n)
    (hk : k ∈ permutationGoodSet n a) :
    (fun i => k (σ i)) ∈ permutationGoodSet n a := by
  intro τ
  have hc := hk (σ * τ)
  have hs := hk σ
  exact hc.trans hs.symm

theorem permutationGoodSet_permutation (n : ℕ) (a : GW.Fock.Coordinates n → ℝ)
    (σ : Equiv.Perm (Fin n)) (k : GW.Fock.Coordinates n) :
    (fun i => k (σ i)) ∈ permutationGoodSet n a ↔ k ∈ permutationGoodSet n a := by
  constructor
  · intro h
    have hi := permutationGoodSet_stable n a σ.symm (fun i => k (σ i)) h
    simpa only [Equiv.apply_symm_apply] using hi
  · exact permutationGoodSet_stable n a σ k

theorem permutationGoodSet_measurable (n : ℕ) (a : GW.Fock.Coordinates n → ℝ)
    (ha : Measurable a) : MeasurableSet (permutationGoodSet n a) := by
  have he : permutationGoodSet n a = ⋂ τ : Equiv.Perm (Fin n),
      {k | a (fun i => k (τ i)) = a k} := by
    ext k
    simp only [permutationGoodSet, Set.mem_setOf_eq, Set.mem_iInter]
  rw [he]
  apply MeasurableSet.iInter
  intro τ
  exact measurableSet_eq_fun (ha.comp (Measurable.of_eval (fun i => measurable_pi_apply (τ i)))) ha

def aeInvariantRepresentative (n : ℕ) (a : GW.Fock.Coordinates n → ℝ) :
    GW.Fock.Coordinates n → ℝ := (permutationGoodSet n a).indicator a

theorem aeInvariantRepresentative_measurable (n : ℕ) (a : GW.Fock.Coordinates n → ℝ)
    (ha : Measurable a) : Measurable (aeInvariantRepresentative n a) :=
  ha.indicator (permutationGoodSet_measurable n a ha)

theorem aeInvariantRepresentative_permutation (n : ℕ) (a : GW.Fock.Coordinates n → ℝ)
    (σ : Equiv.Perm (Fin n)) (k : GW.Fock.Coordinates n) :
    aeInvariantRepresentative n a (fun i => k (σ i)) = aeInvariantRepresentative n a k := by
  classical
  by_cases hk : k ∈ permutationGoodSet n a
  · have hs := (permutationGoodSet_permutation n a σ k).mpr hk
    simp only [aeInvariantRepresentative, Set.indicator_of_mem hk, Set.indicator_of_mem hs]
    exact hk σ
  · have hs := mt (permutationGoodSet_permutation n a σ k).mp hk
    simp only [aeInvariantRepresentative, Set.indicator_of_notMem hk, Set.indicator_of_notMem hs]

theorem aeInvariantRepresentative_ae (n : ℕ) (a : GW.Fock.Coordinates n → ℝ)
    (ha : ∀ τ : Equiv.Perm (Fin n),
      (fun k => a (fun i => k (τ i))) =ᵐ[GW.Fock.sectorMeasure n] a) :
    aeInvariantRepresentative n a =ᵐ[GW.Fock.sectorMeasure n] a := by
  filter_upwards [ae_all_iff.mpr ha] with k hk
  exact Set.indicator_of_mem hk a

theorem fockRealMultiplier_domain_congr_ae
    (m t : ∀ n, GW.Fock.Coordinates n → ℝ)
    (he : ∀ n, m n =ᵐ[GW.Fock.sectorMeasure n] t n) :
    (fockRealMultiplier m).domain = (fockRealMultiplier t).domain := by
  ext u
  rw [fockRealMultiplier_domain_iff, fockRealMultiplier_domain_iff]
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨v,fun n => ?_⟩
    filter_upwards [hv n, he n] with k hk heq
    simpa only [heq] using hk
  · rintro ⟨v,hv⟩
    refine ⟨v,fun n => ?_⟩
    filter_upwards [hv n, he n] with k hk heq
    simpa only [heq] using hk

theorem fockRealMultiplier_dense_of_ae_permutation
    (m : ∀ n, GW.Fock.Coordinates n → ℝ) (hm : ∀ n, Measurable (m n))
    (hp : ∀ n (τ : Equiv.Perm (Fin n)),
      (fun k => m n (fun i => k (τ i))) =ᵐ[GW.Fock.sectorMeasure n] m n) :
    Dense ((fockRealMultiplier m).domain : Set GW.Fock.Carrier) := by
  let t := fun n => aeInvariantRepresentative n (m n)
  have htm : ∀ n, Measurable (t n) := fun n => aeInvariantRepresentative_measurable n (m n) (hm n)
  have htp : ∀ n (τ : Equiv.Perm (Fin n)) k, t n (fun i => k (τ i)) = t n k :=
    fun n τ k => aeInvariantRepresentative_permutation n (m n) τ k
  have he : (fockRealMultiplier m).domain = (fockRealMultiplier t).domain :=
    fockRealMultiplier_domain_congr_ae m t (fun n => (aeInvariantRepresentative_ae n (m n) (hp n)).symm)
  rw [he]
  exact fockRealMultiplier_dense t htm htp

end Froehlich
