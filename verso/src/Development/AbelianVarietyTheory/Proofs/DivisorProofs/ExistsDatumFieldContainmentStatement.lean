import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDatumFieldContainment
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FieldEnlarge.exists_record_le_fieldLL` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsDatumFieldContainment.lean&line=300#L300)
-/
theorem _root_.GlobalTheory.T.exists_datum_field_containment : ∀ (D : D7) (K : IntermediateField ℚ ℂ), FiniteDimensional ℚ K → ∃ D' : D7, D'.R = D.R ∧ HEq D'.host D.host ∧ K ≤ GlobalTheory.ShFam.fieldLL D' := by
  first | exact @GlobalTheory.FieldEnlarge.exists_record_le_fieldLL | exact GlobalTheory.FieldEnlarge.exists_record_le_fieldLL | (intros; apply GlobalTheory.FieldEnlarge.exists_record_le_fieldLL <;> assumption)
