import Froehlich.Nodes.DF01
import GW.Fock.Sectors

/-! Logical clause contract for thm:target/MN03. This definition is not a
proof of the main theorem. The actual family must be the GW06 fiber form
operators; accepting that defining family remains a separate required gate. -/
namespace Froehlich

/-- The exact target clauses, on the canonical GW fiber Hilbert space. -/
def MainStatement
    (H : ℝ → GW.Space → (GW.Fock.Carrier →ₗ.[ℂ] GW.Fock.Carrier)) : Prop :=
  ∃ gStar : ℝ, 0 < gStar ∧ ∀ (g : ℝ) (P : GW.Space),
    |g| < gStar → ‖P‖ ≤ 1 / 4 →
      (realSpectrum (H g P) ∩ Set.Iio (groundEnergy (H g 0) + 1) =
        {groundEnergy (H g P)}) ∧
      HasEigenvector (H g P) (groundEnergy (H g P))

end Froehlich
