import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RefLowerOfFibreInput
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FRefLowerOfFibreInput.lean&line=203#L203)
-/
theorem _root_.GlobalTheory.T.ref_lower_of_fibre_input : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (j k : ℕ) (R : RootModel Ψ (j + 1 + (k + 1))), AmpleQ R.y R.A.a → FlatUnit R → FibreInput R → RefLower R := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.RefLow.refLower_of_fibre | exact GlobalTheory.CompanionTheory.Ar.Ht.RefLow.refLower_of_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.RefLow.refLower_of_fibre <;> assumption)
