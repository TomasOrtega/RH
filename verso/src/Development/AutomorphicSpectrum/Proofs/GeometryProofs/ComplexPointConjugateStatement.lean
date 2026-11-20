import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointConjugate
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Flat.ptOver_conj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FComplexPointConjugate.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.complex_point_conjugate : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) (z : (Σ k, ι k) → ℂ), PtOver y φ σ z → PtOver y φ (ComplexEmbedding.conjugate σ) (fun p => (starRingEnd ℂ) (z p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ptOver_conj | exact GlobalTheory.CompanionTheory.Ar.Flat.ptOver_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ptOver_conj <;> assumption)
