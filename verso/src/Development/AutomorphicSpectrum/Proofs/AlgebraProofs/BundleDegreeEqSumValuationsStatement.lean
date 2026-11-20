import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BundleDegreeEqSumValuations
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FBundleDegreeEqSumValuations.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.bundle_degree_eq_sum_valuations : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (n : ℕ) (b₀ : Module.Basis (Fin n) K V) (b : C.I → Module.Basis (Fin n) K V), IsBun C L → (∀ i, IsLatOf C i (b i) (L i)) → {i | C.v i (b₀.det (b i)) ≠ 1}.Finite ∧ deg C L = ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (b₀.det (b i))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula | exact GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula <;> assumption)
