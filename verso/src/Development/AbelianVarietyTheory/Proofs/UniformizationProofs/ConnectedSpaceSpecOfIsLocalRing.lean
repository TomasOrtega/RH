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
Use `hB.smooth` as an intermediate fact. Use `hB.geomConnected` as an intermediate fact. Establish `: ConnectedSpace B.left` using `(GroupConn.connectedSpace_group S B).1`. Take `⟨x⟩ : Nonempty B.left` from `inferInstance`. Conclude with `exists_dim_of_preconnected B.hom x`.
-/
theorem exists_relDim_of_connected {S : Scheme.{0}} [ConnectedSpace S] (B : Over S) [GrpObj B]
    (hB : IsAbelianScheme B) : ∃ g, SmoothOfRelativeDimension g B.hom := by
  have := hB.smooth
  have := hB.geomConnected
  have : ConnectedSpace B.left := (GroupConn.connectedSpace_group S B).1
  obtain ⟨x⟩ : Nonempty B.left := inferInstance
  exact exists_dim_of_preconnected B.hom x

/- English proof (translation)
Use `show ConnectedSpace (PrimeSpectrum A)`. Rewrite using `[connectedSpace_iff_univ]`. Use `⟨⟨IsLocalRing.closedPoint A, trivial⟩, ?_⟩` and prove the remaining obligations. Introduce `u v hu hv huv ⟨x, _, hx⟩ ⟨y, _, hy⟩`. Establish `hc : IsLocalRing.closedPoint A ∈ u ∪ v` using `huv trivial`.

Break down `hc with h | h` into its components or cases. Conclude with `⟨y, trivial, (IsLocalRing.specializes_closedPoint y).mem_open hu h, hy⟩`. Conclude with `⟨x, trivial, hx, (IsLocalRing.specializes_closedPoint x).mem_open hv h⟩`.
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
Introduce `A _ _ B _ hB`. Use `connectedSpace_spec_of_isLocalRing A` as an intermediate fact. Conclude with `exists_relDim_of_connected B hB`.
-/
theorem exists_relDim : ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B], IsAbelianScheme B → ∃ g, SmoothOfRelativeDimension g B.hom := by
  intro A _ _ B _ hB
  have := connectedSpace_spec_of_isLocalRing A
  exact exists_relDim_of_connected B hB

end GlobalTheory.AbelianDim
