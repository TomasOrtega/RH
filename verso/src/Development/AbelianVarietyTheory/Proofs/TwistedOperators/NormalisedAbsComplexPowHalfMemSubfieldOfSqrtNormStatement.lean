import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedAbsComplexPowHalfMemSubfieldOfSqrtNorm
import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FNormalisedAbsComplexPowHalfMemSubfieldOfSqrtNorm.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.normalisedAbsComplexPow_half_mem_subfield_of_sqrt_norm : ∀ {D : D7} (F : Subfield ℂ) (w : Pl D.host.E), ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ F → ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ F := by
  first | exact @GlobalTheory.HalfPowField.apow_half_mem_of_sqrt | exact GlobalTheory.HalfPowField.apow_half_mem_of_sqrt | (intros; apply GlobalTheory.HalfPowField.apow_half_mem_of_sqrt <;> assumption)
