import Froehlich

#check @Froehlich.main
#print axioms Froehlich.main
#print Froehlich.MainStatement

open Lean Elab Command in
run_elab do
  let ci ← getConstInfo ``Froehlich.main
  let expanded ← Lean.Meta.whnf ci.type
  logInfo m!"Fully expanded main type: {expanded}"

example :
    ∃ gStar : ℝ, 0 < gStar ∧ ∀ (g : ℝ) (P : GW.Space),
      |g| < gStar → ‖P‖ ≤ 1/4 →
        (Froehlich.realSpectrum (Froehlich.fiberHamiltonian g P) ∩
          Set.Iio (Froehlich.groundEnergy (Froehlich.fiberHamiltonian g 0)+1) =
          {Froehlich.groundEnergy (Froehlich.fiberHamiltonian g P)}) ∧
        Froehlich.HasEigenvector (Froehlich.fiberHamiltonian g P)
          (Froehlich.groundEnergy (Froehlich.fiberHamiltonian g P)) := Froehlich.main
