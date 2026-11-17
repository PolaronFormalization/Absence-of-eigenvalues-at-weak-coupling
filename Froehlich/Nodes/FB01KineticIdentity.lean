import Froehlich.Nodes.FB01Kinetic

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

theorem coreKineticComponent_sector_identity (P : GW.Space) (u : boundedMomentumCore) (n : ℕ) :
    (∑ a : Fin 3, ‖coreKineticComponent P a u n‖^2) +
        (n : ℝ) * ‖(u : GW.Fock.Carrier) n‖^2 =
      freeSectorEnergy P n ((u : GW.Fock.Carrier) n) := by
  have hi (a : Fin 3) := fockRealMultiplier_sector_norm_sq
    (fun n K => totalMomentum n K a-P a) (u : GW.Fock.Carrier)
    (coreKineticComponent P a u) (coreKineticComponent_graph P a u) n
  have hn : Integrable (fun K => (n : ℝ) * ‖physicalSector n ((u : GW.Fock.Carrier) n) K‖^2)
      (GW.Fock.sectorMeasure n) :=
    ((Lp.memLp (physicalSector n ((u : GW.Fock.Carrier) n))).integrable_norm_pow
      (p := 2) (by norm_num)).const_mul (n : ℝ)
  have hu : ‖(u : GW.Fock.Carrier) n‖^2 =
      ∫ K, ‖physicalSector n ((u : GW.Fock.Carrier) n) K‖^2 ∂GW.Fock.sectorMeasure n := by
    rw [← (physicalSector n).norm_map ((u : GW.Fock.Carrier) n), GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  have hs : (∑ a : Fin 3, ‖coreKineticComponent P a u n‖^2) =
      ∫ K, ∑ a : Fin 3, (totalMomentum n K a-P a)^2 *
        ‖physicalSector n ((u : GW.Fock.Carrier) n) K‖^2 ∂GW.Fock.sectorMeasure n := by
    calc
      _ = ∑ a : Fin 3, ∫ K, (totalMomentum n K a-P a)^2 *
          ‖physicalSector n ((u : GW.Fock.Carrier) n) K‖^2 ∂GW.Fock.sectorMeasure n :=
        Finset.sum_congr rfl (fun a _ => (hi a).2)
      _ = _ := (integral_finsetSum Finset.univ (fun a _ => (hi a).1)).symm
  rw [hs,hu,← integral_const_mul]
  rw [← integral_add (integrable_finsetSum Finset.univ (fun a _ => (hi a).1)) hn]
  apply integral_congr_ae
  exact Eventually.of_forall (fun K => by
    change (∑ a : Fin 3, (totalMomentum n K a-P a)^2 *
      ‖physicalSector n ((u : GW.Fock.Carrier) n) K‖^2) +
        (n : ℝ) * ‖physicalSector n ((u : GW.Fock.Carrier) n) K‖^2 = _
    rw [← Finset.sum_mul]
    have he : (∑ a : Fin 3, (totalMomentum n K a-P a)^2) = ‖totalMomentum n K-P‖^2 := by
      simpa using (EuclideanSpace.real_norm_sq_eq (totalMomentum n K-P)).symm
    rw [he]
    unfold freeSymbol
    ring)

theorem coreKineticNumber_identity (P : GW.Space) (u : boundedMomentumCore) :
    (∑ a : Fin 3, ‖coreKineticComponent P a u‖^2) +
        ‖GW.Fock.numberPower GW.Fock.Sector (1/2) (numberFormRootInput (coreNumberLift u))‖^2 =
      freeEnergy P (u : GW.Fock.Carrier) := by
  have hf := freeSectorEnergy_summable P (coreEnergyLift P u)
  rw [coreEnergyLift_embedding] at hf
  have hs : Summable (fun n => ∑ a : Fin 3, ‖coreKineticComponent P a u n‖^2) :=
    Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (coreKineticComponent_sector_bound P u) hf
  have hn := numberFormRoot_summable (coreNumberLift u)
  rw [coreNumberLift_embedding] at hn
  have hnorm := numberFormRoot_norm (coreNumberLift u)
  rw [coreNumberLift_embedding] at hnorm
  have hd (a : Fin 3) : Summable (fun n => ‖coreKineticComponent P a u n‖^2) :=
    (GW.Analysis.memℓp_two_iff_sq _).mp (coreKineticComponent P a u).property
  have he : (∑' n, ∑ a : Fin 3, ‖coreKineticComponent P a u n‖^2) =
      ∑ a : Fin 3, ‖coreKineticComponent P a u‖^2 := by
    rw [Summable.tsum_finsetSum (fun a _ => hd a)]
    simp_rw [← GW.Fock.carrier_norm_sq]
  rw [← he,hnorm,← Summable.tsum_add hs hn]
  apply tsum_congr
  intro n
  exact coreKineticComponent_sector_identity P u n

end Froehlich
