import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscOverNumberFieldRing
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.ConstEmbedding.exists_embedding` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FHolomorphicDiscOverNumberFieldRing.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.holomorphic_disc_over_number_field_ring : ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (n : ℕ) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X)), IsHolTo (Metric.ball 0 1) p → ∃ τ : F →+* ℂ, ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ q = spMap (τ.comp (algebraMap (𝓞 F) F)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ConstEmbedding.exists_embedding | exact GlobalTheory.CompanionTheory.Ar.ConstEmbedding.exists_embedding | (intros; apply GlobalTheory.CompanionTheory.Ar.ConstEmbedding.exists_embedding <;> assumption)
