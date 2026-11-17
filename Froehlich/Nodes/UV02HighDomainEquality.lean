import Froehlich.Nodes.UV02HighNeumannSolver
import Froehlich.Nodes.UV02HighFreeDomain

/-! Every compressed cutoff associated domain equals the actual full free
maximal domain restricted to that closed high sector. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
private theorem highAssociatedShift_kernel {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (d : GW.Operators.CoerciveFormData V H) (c : ℝ) (hc : d.shift ≤ c)
    (u : (GW.Operators.formOperator d).domain)
    (hz : GW.Operators.formOperator d u+(c : ℂ) • (u : H)=0) : (u : H)=0 := by
  let x := GW.Operators.operatorFormCoordinate d u
  have hx : d.embedding x=(u : H) := GW.Operators.operatorFormCoordinate_embedding d u
  have hform := GW.Operators.formOperator_form_identity d u x
  rw [hx] at hform
  have hi := congrArg (fun z : H => (⟪(u : H),z⟫_ℂ).re) hz
  have hscalar : (⟪(u : H),(c : ℂ) • (u : H)⟫_ℂ).re=c*‖(u : H)‖^2 := by
    rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
    change ((c : ℂ)*(‖(u : H)‖ : ℂ)^2).re=c*‖(u : H)‖^2
    norm_cast
  have hdiag : (d.form x x).re+c*‖(u : H)‖^2=0 := by
    rw [hform]
    simpa only [inner_add_right,Complex.add_re,inner_zero_right,Complex.zero_re,hscalar] using hi
  have hlower := d.lower_bound x
  rw [hx] at hlower
  have hnorm : ‖x‖^2=0 := by
    have hneg : (d.shift-c)*‖(u : H)‖^2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hc) (sq_nonneg _)
    have hprod : d.lower*‖x‖^2 ≤ 0 := by linarith
    have hle : ‖x‖^2 ≤ 0 := by
      by_contra h
      have hpos := mul_pos d.lower_pos (lt_of_not_ge h)
      linarith
    exact le_antisymm hle (sq_nonneg _)
  have hx0 : x=0 := by
    have : ‖x‖=0 := by nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp this
  rw [←hx,hx0,map_zero]


theorem highCutoffDomain_subset_freeDomain (g : ℝ) (P : GW.Space) (n : ℕ)
    (Λ : GW.Operators.PositiveCutoff) :
    (compressedHamiltonian g P n (some Λ)).domain ≤ HighFreePhysicalDomain P n := by
  obtain ⟨c,hc,hshift,hsmall⟩ := highCutoffField_shift_exists g P n Λ
    (compressedFiberFormData g P n (some Λ)).shift
  intro u hu
  let U : (compressedHamiltonian g P n (some Λ)).domain := ⟨u,hu⟩
  let z := compressedHamiltonian g P n (some Λ) U+(c : ℂ) • u
  let v := highCutoffShiftSolution g P n Λ c hc z
  have hvH := highCutoffShiftSolution_mem_cutoff g P n Λ c hc hsmall z
  have hvF := highCutoffShiftSolution_mem_free g P n Λ c hc z
  let W : (compressedHamiltonian g P n (some Λ)).domain := ⟨v,hvH⟩
  have hs := highCutoffShiftSolution_equation g P n Λ c hc hsmall z
  have hz : compressedHamiltonian g P n (some Λ) (U-W)+(c : ℂ) •
      ((U-W : (compressedHamiltonian g P n (some Λ)).domain) : HighSectorSpace n)=0 := by
    have hmap := (compressedHamiltonian g P n (some Λ)).toFun.map_sub U W
    have hco : ((U-W : (compressedHamiltonian g P n (some Λ)).domain) : HighSectorSpace n)=u-v := rfl
    change (compressedHamiltonian g P n (some Λ)).toFun (U-W)+(c : ℂ) •
      ((U-W : (compressedHamiltonian g P n (some Λ)).domain) : HighSectorSpace n)=0
    rw [hmap,hco]
    calc
      _ = (compressedHamiltonian g P n (some Λ) U+(c : ℂ) • u)-
          (compressedHamiltonian g P n (some Λ) W+(c : ℂ) • v) := by
        change (compressedHamiltonian g P n (some Λ)).toFun U-(compressedHamiltonian g P n (some Λ)).toFun W+
          (c : ℂ) • (u-v)=((compressedHamiltonian g P n (some Λ)).toFun U+(c : ℂ) • u)-
            ((compressedHamiltonian g P n (some Λ)).toFun W+(c : ℂ) • v)
        rw [smul_sub]
        abel
      _ = 0 := sub_eq_zero.mpr hs.symm
  have hzero := highAssociatedShift_kernel (compressedFiberFormData g P n (some Λ)) c hshift.le (U-W) hz
  have heq : u=v := sub_eq_zero.mp hzero
  change (u : GW.Fock.Carrier) ∈ (freeFiberOperator P).domain
  rw [heq]
  exact hvF

theorem highCutoffDomain_eq_freeDomain (g : ℝ) (P : GW.Space) (n : ℕ)
    (Λ : GW.Operators.PositiveCutoff) :
    (compressedHamiltonian g P n (some Λ)).domain=HighFreePhysicalDomain P n :=
  le_antisymm (highCutoffDomain_subset_freeDomain g P n Λ) (highFreeDomain_subset_cutoffDomain g P n Λ)

end Froehlich
