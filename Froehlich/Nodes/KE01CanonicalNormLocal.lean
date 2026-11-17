import Froehlich.Nodes.KE01CanonicalNormTools
import Froehlich.Nodes.CA03VariableDifferences

set_option autoImplicit false
noncomputable section
namespace Froehlich
variable {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The ordered derivative identification is local on an arbitrary open set.
It does not require a global smooth extension of the function. -/
theorem coordinateWordPartial_native_on (is : List (Fin d)) (F : (Fin d → ℝ) → V)
    (S : Set (Fin d → ℝ)) (hS : IsOpen S)
    (hF : ContDiffOn ℝ (is.length : ℕ) F S) (q : Fin d → ℝ) (hq : q ∈ S) :
    coordinateWordPartial is F q =
      iteratedFDeriv ℝ is.length F q
        (listDirections (fun i : Fin d => (Pi.single i 1 : Fin d → ℝ)) is) := by
  induction is generalizing q with
  | nil => rfl
  | cons i is ih =>
    have ht : ContDiffOn ℝ (is.length : ℕ) F S := hF.of_le (by simp)
    have he : Set.EqOn (coordinateWordPartial is F)
        (fun p => iteratedFDeriv ℝ is.length F p
          (listDirections (fun j : Fin d => (Pi.single j 1 : Fin d → ℝ)) is)) S :=
      fun p hp => ih ht p hp
    have heq := coordinateIterate_congr_of_isOpen i 1 _ _ S hS he hq
    change coordinatePartial i (coordinateWordPartial is F) q = coordinatePartial i
      (fun p => iteratedFDeriv ℝ is.length F p
        (listDirections (fun j : Fin d => (Pi.single j 1 : Fin d → ℝ)) is)) q at heq
    have hAt : ContDiffAt ℝ ((i::is).length : ℕ) F q := (hF q hq).contDiffAt (hS.mem_nhds hq)
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ is.length F) q :=
      hAt.differentiableAt_iteratedFDeriv
        (by exact_mod_cast (show is.length < (i::is).length by simp))
    have ha := hd.hasFDerivAt.continuousMultilinear_apply_const
      (listDirections (fun j : Fin d => (Pi.single j 1 : Fin d → ℝ)) is)
    rw [coordinateWordPartial,heq,coordinatePartial_eq_fderiv i _ q ha.differentiableAt]
    exact (hd.iteratedFDeriv_succ_apply_left'
      (m := listDirections (fun j : Fin d => (Pi.single j 1 : Fin d → ℝ)) (i::is))).symm

/-- The reverse norm bridge uses only ordinary C^k regularity at the point,
so it also applies at boundary momenta via the prescribed larger open set. -/
theorem coordinateMultiPartial_norm_le_iterated_at (alpha : Fin d → ℕ)
    (F : (Fin d → ℝ) → V) (q : Fin d → ℝ)
    (hF : ContDiffAt ℝ (∑ i, alpha i : ℕ) F q) :
    ‖coordinateMultiPartial alpha F q‖ ≤ ‖iteratedFDeriv ℝ (∑ i, alpha i : ℕ) F q‖ := by
  classical
  have hWithin : ContDiffWithinAt ℝ (∑ i, alpha i : ℕ) F Set.univ q := hF.contDiffWithinAt
  have hfinite : ((∑ i,alpha i : ℕ) : WithTop ENat) ≠ ((⊤ : ENat) : WithTop ENat) := by
    exact_mod_cast ENat.natCast_ne_top (∑ i,alpha i)
  obtain ⟨S,hS,hq,hOn⟩ := hWithin.contDiffOn' (m := (∑ i, alpha i : ℕ)) le_rfl
    (fun h => False.elim (hfinite h))
  simp only [Set.insert_eq_of_mem (Set.mem_univ q),Set.univ_inter] at hOn
  rw [coordinateMultiPartial_eq_unitBlocks,←coordinateWordPartial_unitBlocks,
    coordinateWordPartial_native_on _ F S hS
      (by simpa only [canonicalMultiIndexCoordinates_length] using hOn) q hq]
  have hp : (∏ j : Fin (canonicalMultiIndexCoordinates alpha).length,
      ‖listDirections (fun i : Fin d => (Pi.single i 1 : Fin d → ℝ))
        (canonicalMultiIndexCoordinates alpha) j‖) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    rw [listDirections_eq_get,Pi.norm_single,norm_one]
  have hb := (iteratedFDeriv ℝ (canonicalMultiIndexCoordinates alpha).length F q).le_opNorm
    (listDirections (fun i : Fin d => (Pi.single i 1 : Fin d → ℝ)) (canonicalMultiIndexCoordinates alpha))
  rw [hp,mul_one] at hb
  exact hb.trans_eq (congrArg (fun n : ℕ => ‖iteratedFDeriv ℝ n F q‖)
    (canonicalMultiIndexCoordinates_length alpha))

end Froehlich
