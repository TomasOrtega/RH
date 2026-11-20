import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfSection

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianDim

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem exists_relDim_of_connected {S : Scheme.{0}} [ConnectedSpace S] (B : Over S) [GrpObj B]
    (hB : IsAbelianScheme B) : ∃ g, SmoothOfRelativeDimension g B.hom := by
  have := hB.smooth
  have := hB.geomConnected
  have : ConnectedSpace B.left := (GroupConn.connectedSpace_group S B).1
  obtain ⟨x⟩ : Nonempty B.left := inferInstance
  exact exists_dim_of_preconnected B.hom x

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Supply the required witnesses or components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem connectedSpace_spec_of_isLocalRing (A : Type) [CommRing A] [IsLocalRing A] :
    ConnectedSpace (Spec (CommRingCat.of A)) := by
  show ConnectedSpace (PrimeSpectrum A)
  rw [connectedSpace_iff_univ]
  refine ⟨⟨IsLocalRing.closedPoint A, trivial⟩, ?_⟩
  intro u v hu hv huv ⟨x, _, hx⟩ ⟨y, _, hy⟩
  have hc : IsLocalRing.closedPoint A ∈ u ∪ v := huv trivial
  rcases hc with h | h
  · exact ⟨y, trivial, (IsLocalRing.specializes_closedPoint y).mem_open hu h, hy⟩
  · exact ⟨x, trivial, hx, (IsLocalRing.specializes_closedPoint x).mem_open hv h⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem exists_relDim : ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B], IsAbelianScheme B → ∃ g, SmoothOfRelativeDimension g B.hom := by
  intro A _ _ B _ hB
  have := connectedSpace_spec_of_isLocalRing A
  exact exists_relDim_of_connected B hB

end GlobalTheory.AbelianDim
