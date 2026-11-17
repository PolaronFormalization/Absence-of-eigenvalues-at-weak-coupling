import Froehlich.Nodes.CA02ScalarRemainder
import Froehlich.Nodes.CA02WeightComparison

set_option autoImplicit false

/-! Locally uniform Taylor bounds in the fixed weighted target. The constants
used to prove differentiability may depend on the base parameter; the actual
jet norm bounds are the separately proved source bounds. -/
noncomputable section
namespace Froehlich

def euclideanChartInverseNorm : ℝ :=
  ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap‖

theorem euclideanChart_update_norm_le (p : Fin 3 → ℝ) (i : Fin 3) (u : ℝ) :
    ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm (Function.update p i u)-
      (EuclideanSpace.equiv (Fin 3) ℝ).symm p‖ ≤ euclideanChartInverseNorm*|u-p i| := by
  have hu : Function.update p i u-p = Pi.single i (u-p i) := by
    funext j
    by_cases hji : j = i
    · subst j; simp
    · simp [Function.update_of_ne hji,Pi.single_eq_of_ne hji]
  let L : (Fin 3 → ℝ) →L[ℝ] GW.Space :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap
  calc
    _ = ‖L (Pi.single i (u-p i))‖ := by rw [← map_sub,hu]; rfl
    _ ≤ ‖L‖*‖(Pi.single i (u-p i) : Fin 3 → ℝ)‖ := L.le_opNorm _
    _ = euclideanChartInverseNorm*|u-p i| := by
      rw [Pi.norm_single (G := fun _ : Fin 3 => ℝ) (i := i),Real.norm_eq_abs]
      rfl

theorem auxiliaryInverseWeightJetChart_fixed_weight_remainder
    (is : List (Fin 3)) (n m : ℕ) (e : ℝ) (he : e ≤ 0)
    (p0 : GW.Space) (p : Fin 3 → ℝ) (K : GW.Fock.Coordinates m) (i : Fin 3)
    (t : ℝ) (ht : |t-p i| ≤ 1) :
    |auxiliaryWeight n e p0 m K *
      (auxiliaryInverseWeightJetChart is n e (Function.update p i t) m K-
       auxiliaryInverseWeightJetChart is n e p m K-
       (t-p i)*auxiliaryInverseWeightJetChart (i::is) n e p m K)| ≤
      (scalarDerivativeCoefficientBound (is.length+2)*
        (1+‖p0-(EuclideanSpace.equiv (Fin 3) ℝ).symm p‖+euclideanChartInverseNorm)/2)*|t-p i|^2 := by
  let W := auxiliaryWeight n e p0 m K
  let P := (EuclideanSpace.equiv (Fin 3) ℝ).symm p
  let C := scalarDerivativeCoefficientBound (is.length+2)*
    (1+‖p0-P‖+euclideanChartInverseNorm)
  let f := fun u : ℝ => W*auxiliaryInverseWeightJetChart is n e (Function.update p i u) m K
  let f1 := fun u : ℝ => W*auxiliaryInverseWeightJetChart (i::is) n e (Function.update p i u) m K
  let f2 := fun u : ℝ => W*auxiliaryInverseWeightJetChart (i::i::is) n e (Function.update p i u) m K
  have hd (js : List (Fin 3)) (u : ℝ) : HasDerivAt
      (fun v : ℝ => W*auxiliaryInverseWeightJetChart js n e (Function.update p i v) m K)
      (W*auxiliaryInverseWeightJetChart (i::js) n e (Function.update p i u) m K) u := by
    apply HasDerivAt.const_mul
    simpa only [Function.update_self,Function.update_idem] using
      auxiliaryInverseWeightJetChart_hasDerivAt_update js n m e he (Function.update p i u) K i
  have hderiv : deriv f = f1 := funext (fun u => (hd is u).deriv)
  have hsecond (u : ℝ) : iteratedDeriv 2 f u = f2 u := by
    rw [show (2 : ℕ) = 1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,hderiv]
    exact (hd (i::is) u).deriv
  have hc : ContDiff ℝ 2 f := contDiff_const.mul
    ((auxiliaryInverseWeightJetChart_contDiff is n m e he K 2).comp (contDiff_update 2 p i))
  have hb (u : ℝ) (hu : |u-p i| ≤ 1) : ‖iteratedFDeriv ℝ 2 f u‖ ≤ C := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,hsecond u]
    have hsym := auxiliaryInverseWeightJet_fixed_weight_bound (i::i::is) n m e he p0
      ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Function.update p i u)) K
    have hdu := euclideanChart_update_norm_le p i u
    have hE : 0 ≤ euclideanChartInverseNorm := norm_nonneg _
    have hdP : ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm (Function.update p i u)-P‖ ≤
        euclideanChartInverseNorm := hdu.trans (by nlinarith)
    have htri := norm_sub_le_norm_sub_add_norm_sub p0 P ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Function.update p i u))
    rw [norm_sub_rev P] at htri
    have hcoef := scalarDerivativeCoefficientBound_nonnegative (is.length+2)
    change |W*auxiliaryInverseWeightJetChart (i::i::is) n e (Function.update p i u) m K| ≤ C
    have hsym' : |W*auxiliaryInverseWeightJetChart (i::i::is) n e (Function.update p i u) m K| ≤
        scalarDerivativeCoefficientBound (is.length+2)*
          (1+‖p0-(EuclideanSpace.equiv (Fin 3) ℝ).symm (Function.update p i u)‖) := by
      simpa only [W,auxiliaryInverseWeightJetChart,List.length_cons,Nat.add_assoc] using hsym
    exact hsym'.trans (mul_le_mul_of_nonneg_left (by linarith) hcoef)
  have hsegment (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      |(p i+s • (t-p i))-p i| ≤ 1 := by
    have heq : p i+s • (t-p i)-p i = s*(t-p i) := by simp only [smul_eq_mul]; ring
    rw [heq,abs_mul,abs_of_nonneg hs.1]
    exact (mul_le_mul_of_nonneg_left ht hs.1).trans (by simpa using hs.2)
  have hr := norm_secondTaylor_remainder f (p i) (t-p i) C
    (fun s _ => hc.contDiffAt) (fun s hs => hb _ (hsegment s hs))
  have hp : p i+(t-p i) = t := by ring
  rw [hp,fderiv_eq_smul_deriv,hderiv] at hr
  have heq : f t-f (p i)-(t-p i) • f1 (p i) = W*
      (auxiliaryInverseWeightJetChart is n e (Function.update p i t) m K-
       auxiliaryInverseWeightJetChart is n e p m K-
       (t-p i)*auxiliaryInverseWeightJetChart (i::is) n e p m K) := by
    simp only [f,f1,Function.update_eq_self,smul_eq_mul]
    ring
  rw [heq] at hr
  simpa only [Real.norm_eq_abs,C,P,W,div_mul_eq_mul_div] using hr

end Froehlich
