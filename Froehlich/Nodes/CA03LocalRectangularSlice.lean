import Froehlich.Nodes.CA03LocalRectangularJets
import Froehlich.Nodes.KE01CanonicalNormAffineChain

set_option autoImplicit false
noncomputable section
namespace Froehlich

def rectangularQRInclusion : (GW.Space × GW.Space) →L[ℝ] GW.Space × (GW.Space × GW.Space) :=
  (0 : (GW.Space × GW.Space) →L[ℝ] GW.Space).prod
    (ContinuousLinearMap.id ℝ (GW.Space × GW.Space))

theorem rectangularQR_affine (P : GW.Space) (qr : GW.Space × GW.Space) :
    (P,((0 : GW.Space),0))+rectangularQRInclusion qr = (P,qr) := by
  apply Prod.ext
  · change P+0=P; exact add_zero P
  · change (0 : GW.Space × GW.Space)+qr=qr; exact zero_add qr

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def rectangularMomentumDifference
    (F : (GW.Space × (GW.Space × GW.Space)) → V) (P : GW.Space)
    (qr : GW.Space × GW.Space) : V := F (P,qr)-F (0,qr)

theorem rectangularMomentumDifference_contDiff
    (F : (GW.Space × (GW.Space × GW.Space)) → V)
    (hF : ∀ t ∈ rectangularMomentumSlab, ContDiffAt ℝ 3 F t)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4) :
    ContDiff ℝ 3 (rectangularMomentumDifference F P) := by
  rw [contDiff_iff_contDiffAt]
  intro qr
  have hs (R : GW.Space) (hR : ‖R‖ ≤ 1/4) :
      ContDiffAt ℝ 3 (fun z : GW.Space × GW.Space => F (R,z)) qr := by
    have h := (hF (R,qr) hR).comp qr
      ((contDiffAt_const : ContDiffAt ℝ 3 (fun _ : GW.Space × GW.Space => R) qr).prodMk contDiffAt_id)
    exact h
  exact (hs P hP).sub (hs 0 (by norm_num))

/-- The momentum gain is retained in the full native qr jets, through order two. -/
theorem rectangularMomentumDifference_iterated_bound
    (F : (GW.Space × (GW.Space × GW.Space)) → V) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ t ∈ rectangularMomentumSlab, ContDiffAt ℝ 3 F t)
    (hB : ∀ k ≤ 3, ∀ t ∈ rectangularMomentumSlab, ‖iteratedFDeriv ℝ k F t‖ ≤ M)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4) (n : ℕ) (hn : n ≤ 2)
    (qr : GW.Space × GW.Space) :
    ‖iteratedFDeriv ℝ n (rectangularMomentumDifference F P) qr‖ ≤
      (1+‖rectangularQRInclusion‖)^2*M*‖P‖ := by
  let L := rectangularQRInclusion
  have hc (R : GW.Space) (hR : ‖R‖ ≤ 1/4) :
      ContDiffAt ℝ n (fun z : GW.Space × GW.Space => F (R,z)) qr :=
    ((hF (R,qr) hR).of_le (by exact_mod_cast (show n ≤ 3 by omega))).comp qr
      (contDiffAt_const.prodMk contDiffAt_id)
  have hd := iteratedFDeriv_sub_apply (hc P hP) (hc 0 (by norm_num))
  have hchain (R : GW.Space) (hR : ‖R‖ ≤ 1/4) :
      iteratedFDeriv ℝ n (fun z : GW.Space × GW.Space => F (R,z)) qr =
        (iteratedFDeriv ℝ n F (R,qr)).compContinuousLinearMap (fun _ => L) := by
    have h := iteratedFDeriv_comp_affine_at (R,((0 : GW.Space),0)) L F n qr
      (by rw [rectangularQR_affine]; exact (hF (R,qr) hR).of_le (by exact_mod_cast (show n ≤ 3 by omega)))
    simpa only [L,rectangularQR_affine] using h
  change iteratedFDeriv ℝ n (rectangularMomentumDifference F P) qr = _ at hd
  rw [hchain P hP,hchain 0 (by norm_num)] at hd
  have heq : iteratedFDeriv ℝ n (rectangularMomentumDifference F P) qr =
      (iteratedFDeriv ℝ n F (P,qr)-iteratedFDeriv ℝ n F (0,qr)).compContinuousLinearMap (fun _ => L) := by
    rw [hd]
    ext u
    rfl
  rw [heq]
  have hN := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n F (P,qr)-iteratedFDeriv ℝ n F (0,qr)) (fun _ : Fin n => L)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hN
  have hJ := norm_rectangularMomentum_jet_sub F M hF hB n hn P qr.1 qr.2 hP
  have hp : ‖L‖^n ≤ (1+‖L‖)^2 := by
    interval_cases n <;> (try simp only [pow_zero,pow_one]) <;>
      nlinarith [norm_nonneg L,sq_nonneg ‖L‖]
  exact hN.trans (by
    have h := mul_le_mul hJ hp (pow_nonneg (norm_nonneg L) n)
      (mul_nonneg hM (norm_nonneg P))
    simpa only [L,mul_assoc,mul_comm,mul_left_comm] using h)

end Froehlich
