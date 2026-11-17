import Froehlich.Nodes.CA02AuxiliarySymbols
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

/-! Genuine parameter derivatives of the literal auxiliary weight symbols,
in the source Euclidean coordinate chart, including discarded sectors. -/
noncomputable section
namespace Froehlich

theorem evalScalarDerivativeTerms_contDiff {d : ℕ} (is : List (Fin d))
    (b : ℝ) (hb : 1 ≤ b) (k : ℕ) :
    ContDiff ℝ k (evalScalarTerms (scalarDerivativeTerms is) b) := by
  have h := coordinateBlocksPartial_contDiffOn (is.map (fun i => (i,1))) k
    (scalarInverseRootWeight b) Set.univ isOpen_univ
    (scalarInverseRootWeight_contDiff b hb (k+coordinateBlocksOrder (is.map (fun i => (i,1))) : ℕ)).contDiffOn
  rw [scalarDerivativeTerms_expansion is b hb] at h
  exact contDiffOn_univ.mp h

theorem evalScalarTerms_hasDerivAt_translate {d : ℕ} (ts : List (ScalarWeightTermData d))
    (b : ℝ) (hb : 1 ≤ b) (a p : Fin d → ℝ) (i : Fin d) :
    HasDerivAt (fun t : ℝ => evalScalarTerms ts b (a+Function.update p i t))
      (evalScalarTerms (deriveScalarTerms i ts) b (a+p)) (p i) := by
  have hv : ∀ t : ℝ, a+Function.update p i t = Function.update (a+p) i (a i+t) := by
    intro t
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Pi.add_apply,Function.update_self]
    · simp only [Pi.add_apply,Function.update_of_ne hji]
  have hl : HasDerivAt (fun t : ℝ => a i+t) 1 (p i) := by
    simpa only [id_eq] using (hasDerivAt_id (p i)).const_add (a i)
  have hd := (evalScalarTerms_hasDerivAt_update ts b hb (a+p) i).comp (p i) hl
  convert hd using 1
  · funext t
    change evalScalarTerms ts b (a+Function.update p i t) =
      evalScalarTerms ts b (Function.update (a+p) i (a i+t))
    exact congrArg (evalScalarTerms ts b) (hv t)
  · ring

def auxiliaryInverseWeightJetChart (is : List (Fin 3)) (n : ℕ) (e : ℝ)
    (p : Fin 3 → ℝ) (m : ℕ) (K : GW.Fock.Coordinates m) : ℝ :=
  auxiliaryInverseWeightJet is n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) m K

theorem auxiliaryInverseWeightJetChart_hasDerivAt_update
    (is : List (Fin 3)) (n m : ℕ) (e : ℝ) (he : e ≤ 0)
    (p : Fin 3 → ℝ) (K : GW.Fock.Coordinates m) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => auxiliaryInverseWeightJetChart is n e (Function.update p i t) m K)
      (auxiliaryInverseWeightJetChart (i::is) n e p m K) (p i) := by
  by_cases hnm : n ≤ m
  · have hb := auxiliaryScalarParameter_ge_one n m e he hnm
    simp only [auxiliaryInverseWeightJetChart,auxiliaryInverseWeightJet,if_pos hnm]
    exact evalScalarTerms_hasDerivAt_translate (scalarDerivativeTerms is) _ hb
      (fun j => (totalMomentum m K) j) p i
  · simpa only [auxiliaryInverseWeightJetChart,auxiliaryInverseWeightJet,if_neg hnm,
      if_neg (List.cons_ne_nil i is)] using
      hasDerivAt_const (p i) (if is = [] then (1 : ℝ) else 0)

theorem auxiliaryInverseWeightJetChart_contDiff (is : List (Fin 3)) (n m : ℕ)
    (e : ℝ) (he : e ≤ 0) (K : GW.Fock.Coordinates m) (k : ℕ) :
    ContDiff ℝ k (fun p : Fin 3 → ℝ => auxiliaryInverseWeightJetChart is n e p m K) := by
  by_cases hnm : n ≤ m
  · have hb := auxiliaryScalarParameter_ge_one n m e he hnm
    simp only [auxiliaryInverseWeightJetChart,auxiliaryInverseWeightJet,if_pos hnm]
    exact (evalScalarDerivativeTerms_contDiff is _ hb k).comp (contDiff_const.add contDiff_id)
  · simpa only [auxiliaryInverseWeightJetChart,auxiliaryInverseWeightJet,if_neg hnm] using
      (contDiff_const : ContDiff ℝ k (fun _ : Fin 3 → ℝ => if is = [] then (1 : ℝ) else 0))

theorem auxiliaryInverseWeightJetChart_coordinate_lipschitz
    (is : List (Fin 3)) (n m : ℕ) (e : ℝ) (he : e ≤ 0)
    (p : Fin 3 → ℝ) (K : GW.Fock.Coordinates m) (i : Fin 3) (s t : ℝ) :
    |auxiliaryInverseWeightJetChart is n e (Function.update p i t) m K -
      auxiliaryInverseWeightJetChart is n e (Function.update p i s) m K| ≤
      scalarDerivativeCoefficientBound (is.length+1) * |t-s| := by
  have hd (u : ℝ) : HasDerivAt
      (fun v : ℝ => auxiliaryInverseWeightJetChart is n e (Function.update p i v) m K)
      (auxiliaryInverseWeightJetChart (i::is) n e (Function.update p i u) m K) u := by
    simpa only [Function.update_self,Function.update_idem] using
      auxiliaryInverseWeightJetChart_hasDerivAt_update is n m e he (Function.update p i u) K i
  have hb (u : ℝ) : ‖auxiliaryInverseWeightJetChart (i::is) n e (Function.update p i u) m K‖ ≤
      scalarDerivativeCoefficientBound (is.length+1) := by
    simpa only [auxiliaryInverseWeightJetChart,Real.norm_eq_abs,List.length_cons] using
      auxiliaryInverseWeightJet_bound (i::is) n m e ((EuclideanSpace.equiv (Fin 3) ℝ).symm
        (Function.update p i u)) he K
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u (_ : u ∈ (Set.univ : Set ℝ)) => (hd u).hasDerivWithinAt)
    (fun u (_ : u ∈ (Set.univ : Set ℝ)) => hb u)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ s) (Set.mem_univ t)
  simpa only [Real.norm_eq_abs] using h

end Froehlich
