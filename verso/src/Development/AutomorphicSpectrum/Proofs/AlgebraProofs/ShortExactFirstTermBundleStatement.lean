import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactFirstTermBundle
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Crv.deg_shortExact` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FShortExactFirstTermBundle.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.short_exact_first_term_bundle : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V''), IsBun C L' → ShortExact C L L' L'' f g → IsBun C L ∧ IsBun C L'' ∧ deg C L' = deg C L + deg C L'' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.deg_shortExact | exact GlobalTheory.CompanionTheory.Ar.Crv.deg_shortExact | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.deg_shortExact <;> assumption)
