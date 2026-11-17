import Froehlich.Nodes.CA02CanonicalExpansion
import Froehlich.Nodes.CA03ActualMixed
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false
noncomputable section
namespace Froehlich
variable {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def coordinateWordPartial : List (Fin d) → ((Fin d → ℝ) → V) → (Fin d → ℝ) → V
  | [], F => F
  | i::is, F => coordinatePartial i (coordinateWordPartial is F)

theorem coordinatePartial_contDiff (i : Fin d) (F : (Fin d → ℝ) → V)
    (n : ℕ) (hF : ContDiff ℝ (n+1) F) : ContDiff ℝ n (coordinatePartial i F) := by
  simpa only [contDiffOn_univ] using
    coordinatePartial_contDiffOn i F Set.univ isOpen_univ n hF.contDiffOn

theorem coordinateWordPartial_contDiff (is : List (Fin d)) (F : (Fin d → ℝ) → V)
    (n : ℕ) (hF : ContDiff ℝ (n+is.length : ℕ) F) :
    ContDiff ℝ n (coordinateWordPartial is F) := by
  induction is generalizing n with
  | nil => simpa only [List.length_nil,Nat.add_zero,coordinateWordPartial] using hF
  | cons i is ih =>
    have ht : ContDiff ℝ ((n+1)+is.length : ℕ) F := by
      simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hF
    exact coordinatePartial_contDiff i _ n (ih (n+1) ht)

theorem coordinatePartial_pair_fderiv (F : (Fin d → ℝ) → V)
    (hF : ContDiff ℝ 2 F) (i j : Fin d) (q : Fin d → ℝ) :
    coordinatePartial i (coordinatePartial j F) q =
      fderiv ℝ (fderiv ℝ F) q (Pi.single i 1) (Pi.single j 1) := by
  have hd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hdd : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have he : coordinatePartial j F = (fun p => fderiv ℝ F p (Pi.single j 1)) :=
    funext (fun p => coordinatePartial_eq_fderiv j F p (hd p))
  rw [he]
  have hap : HasFDerivAt (fun p : Fin d → ℝ => fderiv ℝ F p (Pi.single j 1))
      ((ContinuousLinearMap.apply ℝ V (Pi.single j (1 : ℝ))).comp (fderiv ℝ (fderiv ℝ F) q)) q := by
    simpa only [Function.comp_def] using!
      ((ContinuousLinearMap.apply ℝ V (Pi.single j (1 : ℝ))).hasFDerivAt).comp q (hdd q).hasFDerivAt
  rw [coordinatePartial_eq_fderiv i _ q hap.differentiableAt,hap.fderiv]
  rfl

theorem coordinatePartial_comm (F : (Fin d → ℝ) → V) (hF : ContDiff ℝ 2 F)
    (i j : Fin d) :
    coordinatePartial i (coordinatePartial j F) = coordinatePartial j (coordinatePartial i F) := by
  funext q
  rw [coordinatePartial_pair_fderiv F hF,coordinatePartial_pair_fderiv F hF]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by norm_num)) (Pi.single i 1) (Pi.single j 1)

theorem coordinateWordPartial_perm {is js : List (Fin d)} (h : is.Perm js)
    (F : (Fin d → ℝ) → V) (hF : ContDiff ℝ (is.length : ℕ) F) :
    coordinateWordPartial is F = coordinateWordPartial js F := by
  induction h with
  | nil => rfl
  | @cons i is js h ih =>
    have ht : ContDiff ℝ (is.length : ℕ) F := hF.of_le (by simp)
    exact congrArg (coordinatePartial i) (ih ht)
  | swap i j is =>
    have hn : (2+is.length : ℕ) = (j::i::is).length := by simp only [List.length_cons]; omega
    have ht : ContDiff ℝ 2 (coordinateWordPartial is F) :=
      coordinateWordPartial_contDiff is F 2 (by rw [hn]; exact hF)
    exact coordinatePartial_comm _ ht j i
  | @trans is js ks h1 h2 ih1 ih2 =>
    have ht : ContDiff ℝ (js.length : ℕ) F := by simpa only [←h1.length_eq] using hF
    exact (ih1 hF).trans (ih2 ht)

theorem coordinateWordPartial_unitBlocks (is : List (Fin d)) (F : (Fin d → ℝ) → V) :
    coordinateWordPartial is F = coordinateBlocksPartial (is.map (fun i => (i,1))) F := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change coordinatePartial i (coordinateWordPartial is F) =
      coordinateIterate i 1 (coordinateBlocksPartial (is.map (fun j => (j,1))) F)
    rw [coordinateIterate_succ,coordinateIterate_zero,ih]

theorem coordinateWordPartial_native (is : List (Fin d)) (F : (Fin d → ℝ) → V)
    (hF : ContDiff ℝ (is.length : ℕ) F) (q : Fin d → ℝ) :
    coordinateWordPartial is F q =
      iteratedFDeriv ℝ is.length F q
        (listDirections (fun i : Fin d => (Pi.single i 1 : Fin d → ℝ)) is) := by
  induction is generalizing q with
  | nil => rfl
  | cons i is ih =>
    have ht : ContDiff ℝ (is.length : ℕ) F := hF.of_le (by simp)
    have he : coordinateWordPartial is F = (fun p => iteratedFDeriv ℝ is.length F p
        (listDirections (fun j : Fin d => (Pi.single j 1 : Fin d → ℝ)) is)) :=
      funext (fun p => ih ht p)
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ is.length F) q :=
      (hF.differentiable_iteratedFDeriv (by exact_mod_cast (show is.length < (i::is).length by simp))) q
    have ha := hd.hasFDerivAt.continuousMultilinear_apply_const
      (listDirections (fun j : Fin d => (Pi.single j 1 : Fin d → ℝ)) is)
    rw [coordinateWordPartial,he,coordinatePartial_eq_fderiv i _ q ha.differentiableAt]
    exact (hd.iteratedFDeriv_succ_apply_left'
      (m := listDirections (fun j : Fin d => (Pi.single j 1 : Fin d → ℝ)) (i::is))).symm

end Froehlich
