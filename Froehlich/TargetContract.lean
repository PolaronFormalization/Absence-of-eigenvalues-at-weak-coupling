
import Froehlich.Nodes.DF01
import GW.Fock.Sectors

/-! Logical clause contract for thm:target/MN03. This definition is not a
proof of the main theorem. The actual family must be the GW06 fiber form
operators; accepting that defining family remains a separate required 
gate. -/
namespace Froehlich

abbrev MomentumSpace := GW.Space
abbrev FockSpace := GW.Fock.Carrier

noncomputable abbrev groundStateEnergy
    (A : FockSpace →ₗ.[ℂ] FockSpace) : ℝ :=
  groundEnergy A

/-- The exact target clauses, on the canonical GW fiber Hilbert space. -/
def MainStatement
    (H : ℝ → MomentumSpace → (FockSpace →ₗ.[ℂ] FockSpace)) : Prop :=
  ∃ gStar : ℝ, 0 < gStar ∧ ∀ (g : ℝ) (P : MomentumSpace),
    |g| < gStar → ‖P‖ ≤ 1 / 4 →
      (realSpectrum (H g P) ∩
        Set.Iio (groundStateEnergy (H g 0) + 1) =
        {groundStateEnergy (H g P)}) ∧
      HasEigenvector (H g P) (groundStateEnergy (H g P))

end Froehlich

