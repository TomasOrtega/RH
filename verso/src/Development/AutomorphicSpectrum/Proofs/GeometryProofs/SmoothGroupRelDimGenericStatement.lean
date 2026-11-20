import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGroupRelDimGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FSmoothGroupRelDimGeneric.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.smooth_group_rel_dim_generic : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [Smooth G.hom],
    (∀ q : X, genPt ξ ⤳ q) → ∃ g : ℕ, SmoothOfRelativeDimension g G.hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.smoothGrp_relDim | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.smoothGrp_relDim | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.smoothGrp_relDim <;> assumption)
