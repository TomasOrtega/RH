import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldIntegersInIntegrallyClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FNumberFieldIntegersInIntegrallyClosed.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.number_field_integers_in_integrally_closed : ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [IsIntegrallyClosed A] (E : Type) [Field E] [NumberField E] (σ : E →+* Ω) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A Ω).range := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IntEmb.ringOfIntegers_embedding_mem_range | exact GlobalTheory.CompanionTheory.Ar.IntEmb.ringOfIntegers_embedding_mem_range | (intros; apply GlobalTheory.CompanionTheory.Ar.IntEmb.ringOfIntegers_embedding_mem_range <;> assumption)
