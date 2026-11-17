import Froehlich.Nodes.UV02NeumannSolver

/-! Strict form lower bounds identify the Neumann solution with every
associated-domain vector, proving equality of the actual full domains. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

private theorem associatedShift_kernel {V H : Type*}
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

theorem cutoffDomain_subset_freeDomain (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) :
    (cutoffHamiltonian g P Λ).domain ≤ (freeFiberOperator P).domain := by
  obtain ⟨c,hc,hshift,hsmall⟩ := cutoffField_neumann_shift_exists g P Λ
    (fiberFormData g P (some Λ)).shift
  intro u hu
  let U : (cutoffHamiltonian g P Λ).domain := ⟨u,hu⟩
  let z := cutoffHamiltonian g P Λ U+(c : ℂ) • u
  let v := cutoffShiftSolution g P Λ c hc z
  have hvH := cutoffShiftSolution_mem_cutoff g P Λ c hc hsmall z
  have hvF := cutoffShiftSolution_mem_free g P Λ c hc z
  let W : (cutoffHamiltonian g P Λ).domain := ⟨v,hvH⟩
  have hs := cutoffShiftSolution_equation g P Λ c hc hsmall z
  have hz : cutoffHamiltonian g P Λ (U-W)+(c : ℂ) • ((U-W : (cutoffHamiltonian g P Λ).domain) : GW.Fock.Carrier)=0 := by
    have hmap := (cutoffHamiltonian g P Λ).toFun.map_sub U W
    have hco : ((U-W : (cutoffHamiltonian g P Λ).domain) : GW.Fock.Carrier)=u-v := rfl
    change (cutoffHamiltonian g P Λ).toFun (U-W)+(c : ℂ) •
      ((U-W : (cutoffHamiltonian g P Λ).domain) : GW.Fock.Carrier)=0
    rw [hmap,hco]
    calc
      _ = (cutoffHamiltonian g P Λ U+(c : ℂ) • u)-
          (cutoffHamiltonian g P Λ W+(c : ℂ) • v) := by
        change (cutoffHamiltonian g P Λ).toFun U-(cutoffHamiltonian g P Λ).toFun W+
          (c : ℂ) • (u-v)=((cutoffHamiltonian g P Λ).toFun U+(c : ℂ) • u)-
            ((cutoffHamiltonian g P Λ).toFun W+(c : ℂ) • v)
        rw [smul_sub]
        abel
      _ = 0 := sub_eq_zero.mpr hs.symm
  have hzero := associatedShift_kernel (fiberFormData g P (some Λ)) c hshift.le (U-W) hz
  have heq : u=v := sub_eq_zero.mp hzero
  rw [heq]
  exact hvF

theorem cutoffDomain_eq_freeDomain (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) :
    (cutoffHamiltonian g P Λ).domain=(freeFiberOperator P).domain :=
  le_antisymm (cutoffDomain_subset_freeDomain g P Λ) (freeDomain_subset_cutoffDomain g P Λ)

end Froehlich
