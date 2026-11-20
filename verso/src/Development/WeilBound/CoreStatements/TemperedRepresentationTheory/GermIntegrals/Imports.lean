import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.StepSt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3

namespace PositivityTheory.Tls2.Ming3

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem cov : CovSt := by
  intro k _ _ _ _ _ _ ν hν n r h g Φ
  haveI : ν.IsAddHaarMeasure := hν.1
  rw [GlobalTheory.SplitWeil.integral_comp_mul_mul_volM ν g h Φ]
  simp only [Fintype.card_fin, Complex.real_smul]

end PositivityTheory.Tls2.Ming3
