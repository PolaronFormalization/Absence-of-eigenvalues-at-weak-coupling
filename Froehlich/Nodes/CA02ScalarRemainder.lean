import Froehlich.Nodes.CA02AuxiliarySymbolDerivatives
import Froehlich.Nodes.CA01Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Asymptotics.Lemmas

set_option autoImplicit false

/-! Uniform quadratic remainders for the genuine scalar coordinate symbols.
These estimates transfer to operator norm via the retained multiplier bound. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich

theorem auxiliaryInverseWeightJetChart_coordinate_remainder
    (is : List (Fin 3)) (n m : ℕ) (e : ℝ) (he : e ≤ 0)
    (p : Fin 3 → ℝ) (K : GW.Fock.Coordinates m) (i : Fin 3) (t : ℝ) :
    |auxiliaryInverseWeightJetChart is n e (Function.update p i t) m K -
      auxiliaryInverseWeightJetChart is n e p m K -
      (t-p i)*auxiliaryInverseWeightJetChart (i::is) n e p m K| ≤
      scalarDerivativeCoefficientBound (is.length+2)*|t-p i|^2/2 := by
  let f := fun u : ℝ => auxiliaryInverseWeightJetChart is n e (Function.update p i u) m K
  let f1 := fun u : ℝ => auxiliaryInverseWeightJetChart (i::is) n e (Function.update p i u) m K
  let f2 := fun u : ℝ => auxiliaryInverseWeightJetChart (i::i::is) n e (Function.update p i u) m K
  have hd (js : List (Fin 3)) (u : ℝ) : HasDerivAt
      (fun v : ℝ => auxiliaryInverseWeightJetChart js n e (Function.update p i v) m K)
      (auxiliaryInverseWeightJetChart (i::js) n e (Function.update p i u) m K) u := by
    simpa only [Function.update_self,Function.update_idem] using
      auxiliaryInverseWeightJetChart_hasDerivAt_update js n m e he (Function.update p i u) K i
  have hderiv : deriv f = f1 := funext (fun u => (hd is u).deriv)
  have hsecond (u : ℝ) : iteratedDeriv 2 f u = f2 u := by
    rw [show (2 : ℕ) = 1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,hderiv]
    exact (hd (i::is) u).deriv
  have hc : ContDiff ℝ 2 f :=
    (auxiliaryInverseWeightJetChart_contDiff is n m e he K 2).comp (contDiff_update 2 p i)
  have hb (u : ℝ) : ‖iteratedFDeriv ℝ 2 f u‖ ≤ scalarDerivativeCoefficientBound (is.length+2) := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,hsecond u]
    simpa only [f2,auxiliaryInverseWeightJetChart,List.length_cons,Real.norm_eq_abs,Nat.add_assoc] using
      auxiliaryInverseWeightJet_bound (i::i::is) n m e
        ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Function.update p i u)) he K
  have ht := norm_secondTaylor_remainder f (p i) (t-p i)
    (scalarDerivativeCoefficientBound (is.length+2))
    (fun u _ => hc.contDiffAt) (fun u _ => hb _)
  have hp : p i+(t-p i) = t := by ring
  rw [hp,fderiv_eq_smul_deriv,hderiv] at ht
  simpa only [f,f1,Function.update_eq_self,Real.norm_eq_abs,smul_eq_mul] using ht

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem hasDerivAt_of_uniform_quadratic_remainder (F : ℝ → V) (D : V) (x C : ℝ)
    (h : ∀ t, ‖F t-F x-(t-x) • D‖ ≤ C*‖t-x‖^2) : HasDerivAt F D x := by
  apply HasDerivAt.of_isLittleO
  have hb : (fun t => F t-F x-(t-x) • D) =O[𝓝 x] (fun t => ‖t-x‖^2) :=
    Asymptotics.IsBigO.of_bound C (Eventually.of_forall (fun t => by
      simpa only [norm_pow,norm_norm] using h t))
  exact hb.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub x (by norm_num : 1 < (2 : ℕ)))

end Froehlich
