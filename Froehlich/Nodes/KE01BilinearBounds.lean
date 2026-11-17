import Froehlich.Nodes.KE01JointRegularity
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
noncomputable section
namespace Froehlich

/-- The finite binomial bound through order three, applied to the native
Leibniz theorem without changing any differentiation convention. -/
theorem ke01_bilinear_native_bound {D V W Z : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (B : V →L[ℝ] W →L[ℝ] Z) (F : D → V) (G : D → W)
    (hF : ContDiff ℝ 3 F) (hG : ContDiff ℝ 3 G)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hFB : ∀ i ≤ 3,∀ x,‖iteratedFDeriv ℝ i F x‖ ≤ A)
    (hGB : ∀ i ≤ 3,∀ x,‖iteratedFDeriv ℝ i G x‖ ≤ C)
    (k : ℕ) (hk : k ≤ 3) (x : D) :
    ‖iteratedFDeriv ℝ k (fun y => B (F y) (G y)) x‖ ≤ ‖B‖*8*A*C := by
  have h := B.norm_iteratedFDeriv_le_of_bilinear hF hG x (by exact_mod_cast hk)
  have hs : (∑ i ∈ Finset.range (k+1),(k.choose i : ℝ)) ≤ 8 := by
    interval_cases k <;> norm_num [Finset.sum_range_succ]
  have ht : (∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*
      ‖iteratedFDeriv ℝ i F x‖*‖iteratedFDeriv ℝ (k-i) G x‖) ≤
      ∑ i ∈ Finset.range (k+1),(k.choose i : ℝ)*A*C := by
    apply Finset.sum_le_sum
    intro i hi
    have hi3 : i ≤ 3 := by have hri := Finset.mem_range.mp hi; omega
    have hdiff : k-i ≤ 3 := (Nat.sub_le k i).trans hk
    have hm := mul_le_mul (hFB i hi3 x) (hGB (k-i) hdiff x)
      (norm_nonneg (iteratedFDeriv ℝ (k-i) G x)) hA
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm
      (Nat.cast_nonneg (k.choose i) : (0 : ℝ) ≤ (k.choose i : ℝ))
  have heq : (∑ i ∈ Finset.range (k+1),(k.choose i : ℝ)*A*C) =
      (∑ i ∈ Finset.range (k+1),(k.choose i : ℝ))*A*C := by
    rw [Finset.sum_mul,Finset.sum_mul]
  have ht' : (∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*
      ‖iteratedFDeriv ℝ i F x‖*‖iteratedFDeriv ℝ (k-i) G x‖) ≤ 8*A*C := by
    rw [heq] at ht
    exact ht.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hs hA) hC)
  exact h.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left ht' (norm_nonneg B))

local instance ke01BilinearFockReal : NormedSpace ℝ GW.Fock.Carrier := NormedSpace.restrictScalars ℝ ℂ _

/-- The full complex Hilbert inner product, real bilinear for real calculus. -/
def ke01_complexInner : GW.Fock.Carrier →L[ℝ] GW.Fock.Carrier →L[ℝ] ℂ :=
  (isBoundedBilinearMap_inner (𝕜 := ℂ) (E := GW.Fock.Carrier)).toContinuousLinearMap

@[simp] theorem ke01_complexInner_apply (u v : GW.Fock.Carrier) :
    ke01_complexInner u v = inner ℂ u v := rfl

end Froehlich
