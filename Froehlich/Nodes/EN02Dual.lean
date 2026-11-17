import Froehlich.Nodes.BA01

/-! The general coordinate-change clause of EN02. All inverses below are
actual two-sided bounded inverses, on the stated Hilbert coordinate spaces. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
section CoordinateChange
variable {V W H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def transportFormOperator (I : W →L[ℂ] V) (T : V →L[ℂ] V) : W →L[ℂ] W :=
  I.adjoint.comp (T.comp I)

theorem transportFormOperator_spec (I : W →L[ℂ] V) (T : V →L[ℂ] V) (v u : W) :
    ⟪I v, T (I u)⟫_ℂ = ⟪v, transportFormOperator I T u⟫_ℂ := by
  exact (I.adjoint_inner_right v (T (I u))).symm

theorem transportLoad_spec (I : W →L[ℂ] V) (z : V) (v : W) :
    ⟪I v, z⟫_ℂ = ⟪v, I.adjoint z⟫_ℂ :=
  (I.adjoint_inner_right v z).symm

/-- The actual conjugate-dual load transforms by precomposition. -/
def transportLoad (I : W →L[ℂ] V) (F : ConjugateLoad V) : ConjugateLoad W :=
  F.comp I

theorem transportLoad_riesz (I : W →L[ℂ] V) (F : ConjugateLoad V) :
    loadRiesz (transportLoad I F) = I.adjoint (loadRiesz F) := by
  apply Eq.symm
  apply loadRiesz_unique
  intro v
  change F (I v) = ⟪v, I.adjoint (loadRiesz F)⟫_ℂ
  rw [loadRiesz_spec]
  exact (I.adjoint_inner_right v (loadRiesz F)).symm

def transportInverse (J : V →L[ℂ] W) (R : V →L[ℂ] V) : W →L[ℂ] W :=
  J.comp (R.comp J.adjoint)

theorem transportInverse_identities
    (I : W →L[ℂ] V) (J : V →L[ℂ] W) (T R : V →L[ℂ] V)
    (hIJ : I.comp J = .id ℂ V) (hJI : J.comp I = .id ℂ W)
    (hTR : T.comp R = .id ℂ V) (hRT : R.comp T = .id ℂ V) :
    (transportFormOperator I T).comp (transportInverse J R) = .id ℂ W ∧
    (transportInverse J R).comp (transportFormOperator I T) = .id ℂ W := by
  have hJIa : I.adjoint.comp J.adjoint = .id ℂ W := by
    have h := congrArg ContinuousLinearMap.adjoint hJI
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using h
  have hIJa : J.adjoint.comp I.adjoint = .id ℂ V := by
    have h := congrArg ContinuousLinearMap.adjoint hIJ
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using h
  constructor
  · unfold transportFormOperator transportInverse
    calc
      (I.adjoint.comp (T.comp I)).comp (J.comp (R.comp J.adjoint)) =
          I.adjoint.comp ((T.comp (I.comp J)).comp (R.comp J.adjoint)) := by
            simp only [ContinuousLinearMap.comp_assoc]
      _ = I.adjoint.comp ((T.comp R).comp J.adjoint) := by
        rw [hIJ, ContinuousLinearMap.comp_id, ContinuousLinearMap.comp_assoc]
      _ = .id ℂ W := by rw [hTR, ContinuousLinearMap.id_comp, hJIa]
  · unfold transportFormOperator transportInverse
    calc
      (J.comp (R.comp J.adjoint)).comp (I.adjoint.comp (T.comp I)) =
          J.comp ((R.comp (J.adjoint.comp I.adjoint)).comp (T.comp I)) := by
            simp only [ContinuousLinearMap.comp_assoc]
      _ = J.comp ((R.comp T).comp I) := by
        rw [hIJa, ContinuousLinearMap.comp_id, ContinuousLinearMap.comp_assoc]
      _ = .id ℂ W := by rw [hRT, ContinuousLinearMap.id_comp, hJI]

theorem transportInverse_physical_solution
    (I : W →L[ℂ] V) (J : V →L[ℂ] W) (R : V →L[ℂ] V)
    (hIJ : I.comp J = .id ℂ V) (hJI : J.comp I = .id ℂ W)
    (j : V →L[ℂ] H) (j' : W →L[ℂ] H) (hj : j.comp I = j') (z : V) :
    j' (transportInverse J R (I.adjoint z)) = j (R z) := by
  have ha : J.adjoint.comp I.adjoint = .id ℂ V := by
    have h := congrArg ContinuousLinearMap.adjoint hIJ
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using h
  have haz : J.adjoint (I.adjoint z) = z := congrArg (fun L : V →L[ℂ] V => L z) ha
  have hij : I (J (R z)) = R z := congrArg (fun L : V →L[ℂ] V => L (R z)) hIJ
  rw [← hj]
  change j (I (J (R (J.adjoint (I.adjoint z))))) = j (R z)
  rw [haz, hij]
end CoordinateChange
end Froehlich
