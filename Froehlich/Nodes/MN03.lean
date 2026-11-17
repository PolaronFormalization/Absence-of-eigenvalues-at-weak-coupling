import Froehlich.Nodes.MN01
import Froehlich.Nodes.MN02
import Froehlich.TargetContract

set_option autoImplicit false
namespace Froehlich

/-- The actual Fröhlich fiber Hamiltonian has exactly its ground energy in the
full real spectrum below E_g(0)+1, with a nonzero operator-domain eigenvector,
uniformly for signed couplings near zero and all closed-quarter momenta. -/
theorem main : MainStatement fiberHamiltonian := by
  obtain ⟨s,hs,hNonzero⟩ := finalMN01
  refine ⟨s,hs,?_⟩
  intro g P hgs hP
  by_cases hg0 : g = 0
  · subst g
    exact freeCoupling_mainCase P hP
  · exact hNonzero g P hg0 hgs hP

end Froehlich
