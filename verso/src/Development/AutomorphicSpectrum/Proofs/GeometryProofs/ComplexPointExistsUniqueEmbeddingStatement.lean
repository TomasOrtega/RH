import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointExistsUniqueEmbedding
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FComplexPointExistsUniqueEmbedding.lean&line=144#L144)
-/
theorem _root_.GlobalTheory.T.complex_point_existsUnique_embedding : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω), OverInt y φ → ∀ z ∈ mcPts (mCoordIdeal y), ∃! σ : F →+* ℂ, PtOver y φ σ z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.existsUnique_ptOver | exact GlobalTheory.CompanionTheory.Ar.Flat.existsUnique_ptOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.existsUnique_ptOver <;> assumption)
