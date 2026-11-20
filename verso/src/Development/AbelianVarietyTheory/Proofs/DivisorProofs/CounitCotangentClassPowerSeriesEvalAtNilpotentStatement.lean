import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Katz.counit_dUnit_evA` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCounitCotangentClassPowerSeriesEvalAtNilpotent.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent : ∀ (k : Type) [CommRing k] (d : ℕ) (A : Type) [CommRing A] [Bialgebra k A] (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)), (∀ i, Coalgebra.counit (R := k) (x i) = 0) → ∀ f : MvPowerSeries (Fin d) k, Coalgebra.counit (R := k) (evA k x hx f) = constantCoeff f ∧ dUnit k (evA k x hx f) = ∑ i, lin f i • dUnit k (x i) := by
  first | exact @GlobalTheory.Katz.counit_dUnit_evA | exact GlobalTheory.Katz.counit_dUnit_evA | (intros; apply GlobalTheory.Katz.counit_dUnit_evA <;> assumption)
