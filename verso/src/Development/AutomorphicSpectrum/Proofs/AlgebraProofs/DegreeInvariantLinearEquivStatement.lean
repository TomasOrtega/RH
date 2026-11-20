import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeInvariantLinearEquiv
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FDegreeInvariantLinearEquiv.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.degree_invariant_linear_equiv : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (e : V ≃ₗ[K] V'), IsBun C L → (∀ i x, x ∈ L i ↔ e x ∈ L' i) → IsBun C L' ∧ deg C L' = deg C L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv.deg_equiv | exact GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv.deg_equiv | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv.deg_equiv <;> assumption)
