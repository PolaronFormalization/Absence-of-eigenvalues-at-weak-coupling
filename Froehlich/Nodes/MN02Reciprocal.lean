import Froehlich.Nodes.FC01Multipliers

/-! The bounded reciprocal used in the source free-coupling argument. -/
noncomputable section
open MeasureTheory
namespace Froehlich

def freeReciprocal (P : GW.Space) (lam : ℝ) (n : ℕ)
    (k : GW.Fock.Coordinates n) : ℝ := (freeSymbol P n k - lam)⁻¹

theorem freeSymbol_zero (P : GW.Space) (k : GW.Fock.Coordinates 0) :
    freeSymbol P 0 k = ‖P‖^2 := by
  simp [freeSymbol, totalMomentum]

theorem freeSymbol_ge_one (P : GW.Space) (n : ℕ) (k : GW.Fock.Coordinates (n+1)) :
    1 ≤ freeSymbol P (n+1) k := by
  unfold freeSymbol
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  nlinarith [sq_nonneg ‖totalMomentum (n+1) k-P‖]

theorem freeSymbol_sub_ne_zero (P : GW.Space) (lam : ℝ) (hl : lam < 1)
    (hv : lam ≠ ‖P‖^2) (n : ℕ) (k : GW.Fock.Coordinates n) :
    freeSymbol P n k-lam ≠ 0 := by
  cases n with
  | zero => rw [freeSymbol_zero]; exact sub_ne_zero.mpr hv.symm
  | succ n => have h := freeSymbol_ge_one P n k; linarith

theorem freeReciprocal_bound (P : GW.Space) (lam : ℝ) (hl : lam < 1)
    (n : ℕ) (k : GW.Fock.Coordinates n) :
    |freeReciprocal P lam n k| ≤ max |(‖P‖^2-lam)⁻¹| (1-lam)⁻¹ := by
  cases n with
  | zero => simp only [freeReciprocal, freeSymbol_zero]; exact le_max_left _ _
  | succ n =>
    have h := freeSymbol_ge_one P n k
    have hd : 0 < freeSymbol P (n+1) k-lam := by linarith
    have hbase : 0 < 1-lam := by linarith
    apply le_trans _ (le_max_right _ _)
    rw [freeReciprocal, abs_of_pos (inv_pos.mpr hd)]
    exact (inv_le_inv₀ hd hbase).mpr (by linarith)

def freeReciprocalAction (P : GW.Space) (lam : ℝ) (hl : lam < 1) :
    GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  boundedFockAction (freeReciprocal P lam)
    (fun n => ((freeSymbol_measurable P n).sub measurable_const).inv)
    (max |(‖P‖^2-lam)⁻¹| (1-lam)⁻¹)
    (le_trans (abs_nonneg _) (le_max_left _ _))
    (freeReciprocal_bound P lam hl)
    (fun n τ k => by simp only [freeReciprocal, freeSymbol_permutation])

theorem freeReciprocalAction_ae (P : GW.Space) (lam : ℝ) (hl : lam < 1)
    (u : GW.Fock.Carrier) (n : ℕ) :
    (fun k => (freeReciprocal P lam n k : ℂ) • physicalSector n (u n) k)
      =ᵐ[GW.Fock.sectorMeasure n]
      physicalSector n (freeReciprocalAction P lam hl u n) :=
  boundedFockAction_ae _ _ _ _ _ _ u n

end Froehlich
