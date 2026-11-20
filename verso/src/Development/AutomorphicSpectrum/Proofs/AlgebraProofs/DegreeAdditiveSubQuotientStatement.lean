import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeAdditiveSubQuotient
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg.deg_eq_subDeg_add_deg_quot` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FDegreeAdditiveSubQuotient.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.degree_additive_sub_quotient : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (W : Submodule K V), IsBun C L → deg C L = subDeg C L W + deg C (quot C L W) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg.deg_eq_subDeg_add_deg_quot | exact GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg.deg_eq_subDeg_add_deg_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg.deg_eq_subDeg_add_deg_quot <;> assumption)
