import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo

namespace GlobalTheory.VarPts

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem isClosed_fromSpec_of_isMaximal : ∀ (F : Type) [Field F] (Y : Var F) (V : Y.X.Opens) (hV : IsAffineOpen V) (p : PrimeSpectrum Γ(Y.X, V)),
    p.asIdeal.IsMaximal → IsClosed ({hV.fromSpec p} : Set Y.X) := by
  intro F _ Y V hV p hp
  have : LocallyOfFiniteType Y.str := inferInstance
  have : JacobsonSpace Y.X := LocallyOfFiniteType.jacobsonSpace Y.str
  have he : Topology.IsOpenEmbedding hV.fromSpec := hV.fromSpec.isOpenEmbedding
  have hc : p ∈ closedPoints (Spec Γ(Y.X, V)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).2 hp
  rw [← he.preimage_closedPoints] at hc
  exact hc

end GlobalTheory.VarPts
