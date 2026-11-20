import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralLeadingMinorFlagDensityPosDef
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLintegralLeadingMinorFlagDensityPosDef.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.lintegral_leadingMinorFlagDensity_posDef : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), A.PosDef → ∫⁻ y : Low m → ℂ, ENNReal.ofReal (dens A y) = ENNReal.ofReal (A.det.re ^ (1 - (m : ℤ)) / flagConst m) := by
  first | exact @GlobalTheory.FlagFibre.FlagInt.lintegral_dens | exact GlobalTheory.FlagFibre.FlagInt.lintegral_dens | (intros; apply GlobalTheory.FlagFibre.FlagInt.lintegral_dens <;> assumption)
