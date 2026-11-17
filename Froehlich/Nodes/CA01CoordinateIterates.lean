import Froehlich.Nodes.CA01BilinearLocal
import Mathlib.Analysis.Calculus.Deriv.Pi

/-! Actual coordinate partial blocks on finite real coordinate space.
The block identity is purely the idempotence of coordinate update; local
regularity and product rules are then transported from native calculus. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich
variable {d : ℕ} {V W Z : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def coordinatePartial (i : Fin d) (F : (Fin d → ℝ) → V) (q : Fin d → ℝ) : V :=
  deriv (fun s : ℝ => F (Function.update q i s)) (q i)

def coordinateIterate (i : Fin d) (n : ℕ) (F : (Fin d → ℝ) → V) : (Fin d → ℝ) → V :=
  (coordinatePartial i)^[n] F

theorem coordinateIterate_zero (i : Fin d) (F : (Fin d → ℝ) → V) :
    coordinateIterate i 0 F = F := rfl

theorem coordinateIterate_succ (i : Fin d) (n : ℕ) (F : (Fin d → ℝ) → V) :
    coordinateIterate i (n+1) F = coordinatePartial i (coordinateIterate i n F) :=
  Function.iterate_succ_apply' (coordinatePartial i) n F

theorem coordinateIterate_eq_iteratedDeriv (i : Fin d) (n : ℕ)
    (F : (Fin d → ℝ) → V) (q : Fin d → ℝ) :
    coordinateIterate i n F q = iteratedDeriv n (fun s : ℝ => F (Function.update q i s)) (q i) := by
  induction n generalizing q with
  | zero => simp only [coordinateIterate_zero,iteratedDeriv_zero,Function.update_eq_self]
  | succ n ih =>
    rw [coordinateIterate_succ,coordinatePartial,iteratedDeriv_succ]
    have he : (fun s : ℝ => coordinateIterate i n F (Function.update q i s)) =
        iteratedDeriv n (fun s : ℝ => F (Function.update q i s)) := by
      funext s
      rw [ih]
      simp only [Function.update_self,Function.update_idem]
    rw [he]

theorem coordinatePartial_eq_fderiv (i : Fin d) (F : (Fin d → ℝ) → V)
    (q : Fin d → ℝ) (hF : DifferentiableAt ℝ F q) :
    coordinatePartial i F q = fderiv ℝ F q (Pi.single i 1) := by
  have hf : HasFDerivAt F (fderiv ℝ F q) (Function.update q i (q i)) := by
    simpa only [Function.update_eq_self] using hF.hasFDerivAt
  exact (hf.comp_hasDerivAt (q i) (hasDerivAt_update q i (q i))).deriv

theorem coordinatePartial_contDiffOn (i : Fin d) (F : (Fin d → ℝ) → V)
    (S : Set (Fin d → ℝ)) (hS : IsOpen S) (n : ℕ)
    (hF : ContDiffOn ℝ (n+1) F S) :
    ContDiffOn ℝ n (coordinatePartial i F) S := by
  have hm : (n : WithTop ENat) + 1 ≤ (n+1 : ℕ) := by simp
  have hd := (hF.fderiv_of_isOpen hS hm).clm_apply
    (contDiffOn_const : ContDiffOn ℝ n (fun _ : Fin d → ℝ => (Pi.single i 1 : Fin d → ℝ)) S)
  apply hd.congr
  intro q hq
  exact coordinatePartial_eq_fderiv i F q
    ((hF.differentiableOn (by simp) q hq).differentiableAt (hS.mem_nhds hq))

theorem coordinateIterate_realBilinear (i : Fin d) (n : ℕ)
    (B : V →L[ℝ] W →L[ℝ] Z) (F : (Fin d → ℝ) → V) (G : (Fin d → ℝ) → W)
    (q : Fin d → ℝ) (hF : ContDiffAt ℝ n F q) (hG : ContDiffAt ℝ n G q) :
    coordinateIterate i n (fun p => B (F p) (G p)) q =
      ∑ j ∈ Finset.range (n+1), n.choose j •
        B (coordinateIterate i j F q) (coordinateIterate i (n-j) G q) := by
  have hf : ContDiffAt ℝ n F (Function.update q i (q i)) := by
    simpa only [Function.update_eq_self] using hF
  have hg : ContDiffAt ℝ n G (Function.update q i (q i)) := by
    simpa only [Function.update_eq_self] using hG
  have hline := (contDiff_update (𝕜 := ℝ) n q i).contDiffAt (x := q i)
  have he := iteratedDeriv_realBilinear B (fun s => F (Function.update q i s))
    (fun s => G (Function.update q i s)) n (q i) (hf.comp (q i) hline) (hg.comp (q i) hline)
  simpa only [coordinateIterate_eq_iteratedDeriv] using he

end Froehlich
