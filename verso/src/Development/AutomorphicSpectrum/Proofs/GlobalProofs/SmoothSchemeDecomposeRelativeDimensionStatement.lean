import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothSchemeDecomposeRelativeDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactSpacePts
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Gaga.exists_clopen_smoothOfRelativeDimension` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FSmoothSchemeDecomposeRelativeDimension.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.smooth_scheme_decompose_relative_dimension : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ), Smooth s → ∃ W : ℕ → X.Opens, (∀ D, IsClosed (W D : Set X)) ∧ (∀ D, SmoothOfRelativeDimension D ((W D).ι ≫ s)) ∧ (⨆ D, W D) = ⊤ ∧ Pairwise fun D D' => W D ⊓ W D' = ⊥ := by
  first | exact @GlobalTheory.CompanionTheory.Gaga.exists_clopen_smoothOfRelativeDimension | exact GlobalTheory.CompanionTheory.Gaga.exists_clopen_smoothOfRelativeDimension | (intros; apply GlobalTheory.CompanionTheory.Gaga.exists_clopen_smoothOfRelativeDimension <;> assumption)
