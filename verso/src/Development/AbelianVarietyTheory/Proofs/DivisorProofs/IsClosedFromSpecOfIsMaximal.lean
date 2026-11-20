import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo

namespace GlobalTheory.VarPts

/- English proof (translation)
Introduce `F _ Y V hV p hp`. Establish `: LocallyOfFiniteType Y.str` using `inferInstance`. Establish `: JacobsonSpace Y.X` using `LocallyOfFiniteType.jacobsonSpace Y.str`. Establish `he : Topology.IsOpenEmbedding hV.fromSpec` using `hV.fromSpec.isOpenEmbedding`. Establish `hc : p ∈ closedPoints (Spec Γ(Y.X, V))` using `(PrimeSpectrum.isClosed_singleton_iff_isMaximal p).2 hp`.

Rewrite `hc` using `[← he.preimage_closedPoints]`. Conclude with `hc`.
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
