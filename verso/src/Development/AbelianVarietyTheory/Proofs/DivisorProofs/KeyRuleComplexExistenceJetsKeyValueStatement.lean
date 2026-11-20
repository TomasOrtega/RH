import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyRuleComplexExistenceJetsKeyValue
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MBLow.ArchProof.arch_of_rule4` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKeyRuleComplexExistenceJetsKeyValue.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.keyRule_complex_existence_jets_key_value : ∀ κ : Rule, Rule4 κ → Arch κ := by
  first | exact @GlobalTheory.MBLow.ArchProof.arch_of_rule4 | exact GlobalTheory.MBLow.ArchProof.arch_of_rule4 | (intros; apply GlobalTheory.MBLow.ArchProof.arch_of_rule4 <;> assumption)
