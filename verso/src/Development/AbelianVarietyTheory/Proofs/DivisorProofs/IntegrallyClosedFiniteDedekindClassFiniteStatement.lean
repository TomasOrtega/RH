import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrallyClosedFiniteDedekindClassFinite
import Mathlib

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IntClosedOrder.isDedekindDomain_and_finite_classGroup` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegrallyClosedFiniteDedekindClassFinite.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.integrally_closed_finite_dedekind_class_finite : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] [Module.Finite ℤ A],
    IsDedekindDomain A ∧ Finite (ClassGroup A) := by
  first | exact @GlobalTheory.IntClosedOrder.isDedekindDomain_and_finite_classGroup | exact GlobalTheory.IntClosedOrder.isDedekindDomain_and_finite_classGroup | (intros; apply GlobalTheory.IntClosedOrder.isDedekindDomain_and_finite_classGroup <;> assumption)
