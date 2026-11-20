import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductFormulaModulusRational
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RatProdFormula.product_formula_half` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FProductFormulaModulusRational.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.product_formula_modulus_rational : ∀ α : ℚˣ, (Function.mulSupport fun v : Pl => mp (Ad3.R.lc v (pri α)) (1 / 2)).Finite ∧
  (∏ᶠ v : Pl, mp (Ad3.R.lc v (pri α)) (1 / 2)) * ((|(α : ℝ)| : ℝ) : ℂ) ^ (1 / 2 : ℂ) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.RatProdFormula.product_formula_half | exact GlobalTheory.CompanionTheory.RatProdFormula.product_formula_half | (intros; apply GlobalTheory.CompanionTheory.RatProdFormula.product_formula_half <;> assumption)
