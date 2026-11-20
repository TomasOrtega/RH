import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinCoefficientsSummable
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSiegelEisensteinCoefficientsSummable.lean&line=288#L288)
-/
theorem _root_.GlobalTheory.T.siegel_eisenstein_coefficients_summable : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)) (φ : Mx D V.rank r → ℂ), 2 * r < V.rank → IsCharAF D.host.F ψ → IsInfFam θ → (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → IsCovolOneH lam 𝓖 → φ ∈ schwartzA θ V.rank r → Summable (fun β : HermE D r => W ψ V μ lam φ β) := by
  first | exact @GlobalTheory.CompanionTheory.WSum.summable_W_of_two_mul_lt_rank | exact GlobalTheory.CompanionTheory.WSum.summable_W_of_two_mul_lt_rank | (intros; apply GlobalTheory.CompanionTheory.WSum.summable_W_of_two_mul_lt_rank <;> assumption)
