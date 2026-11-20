import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeMonoLatticeLe
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Crv.deg_le_deg_of_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FDegreeMonoLatticeLe.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.degree_mono_lattice_le : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L L' : C.I → AddSubgroup V), IsBun C L → IsBun C L' → (∀ i, L i ≤ L' i) → deg C L ≤ deg C L' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.deg_le_deg_of_le | exact GlobalTheory.CompanionTheory.Ar.Crv.deg_le_deg_of_le | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.deg_le_deg_of_le <;> assumption)
