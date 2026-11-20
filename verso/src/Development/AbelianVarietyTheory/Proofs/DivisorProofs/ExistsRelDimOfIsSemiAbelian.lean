import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbelianDim

/- English proof (translation)
Introduce `R _ _ G _ _ hG`. Use `hG.smooth` as an intermediate fact. Use `hG.geomConnected` as an intermediate fact. Establish `: ConnectedSpace (Sp R)` using `AbelianDim.connectedSpace_spec_of_isLocalRing R`. Establish `: ConnectedSpace G.left` using `(GroupConn.connectedSpace_group _ G).1`.

Take `⟨x⟩ : Nonempty G.left` from `inferInstance`. Conclude with `exists_dim_of_preconnected G.hom x`.
-/
theorem exists_relDim_of_isSemiAbelian : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∃ g : ℕ, SmoothOfRelativeDimension g G.hom := by
  intro R _ _ G _ _ hG
  have := hG.smooth
  have := hG.geomConnected
  have : ConnectedSpace (Sp R) := AbelianDim.connectedSpace_spec_of_isLocalRing R
  have : ConnectedSpace G.left := (GroupConn.connectedSpace_group _ G).1
  obtain ⟨x⟩ : Nonempty G.left := inferInstance
  exact exists_dim_of_preconnected G.hom x

end GlobalTheory.SemiAbelianDim
