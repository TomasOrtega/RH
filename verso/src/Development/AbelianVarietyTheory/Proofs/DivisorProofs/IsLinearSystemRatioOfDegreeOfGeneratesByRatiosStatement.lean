import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearSystemRatioOfDegreeOfGeneratesByRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsLinearSystemRatioOfDegreeOfGeneratesByRatios.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.isLinearSystemRatioOfDegree_of_generatesByRatios : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω), GenRatios ev → ∀ (τ : ℕ) (t : Ω), IsRatio ev τ t := by
  first | exact @GlobalTheory.DegVal.isRatio_of_genRatios | exact GlobalTheory.DegVal.isRatio_of_genRatios | (intros; apply GlobalTheory.DegVal.isRatio_of_genRatios <;> assumption)
