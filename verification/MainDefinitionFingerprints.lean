import Froehlich.Nodes.GW06
import Froehlich.TargetContract

/-! Kernel-expression fingerprints for the small meaning-carrying interface. -/
open Lean Elab Command in
run_elab do
  for n in [``Froehlich.MainStatement, ``Froehlich.fiberHamiltonian,
      ``Froehlich.fiberFormData, ``Froehlich.fiberUniformData,
      ``Froehlich.singularInteraction, ``Froehlich.freeFiberForm,
      ``Froehlich.realSpectrum, ``Froehlich.realResolventSet,
      ``Froehlich.groundEnergy, ``Froehlich.HasEigenvector] do
    let ci ← getConstInfo n
    let vh := match ci with
      | .defnInfo d => some (hash d.value)
      | _ => none
    logInfo m!"{n}: typeHash={repr (hash ci.type)} bodyHash={repr vh}"
