import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorEqTeichmullerOfFrobeniusEqPowSelf
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWittVectorEqTeichmullerOfFrobeniusEqPowSelf.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.wittVector_eq_teichmuller_of_frobenius_eq_pow_self : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [CharP O l] [PerfectRing O l] (y : WittVector l O), WittVector.frobenius y = y ^ l → y = WittVector.teichmuller l (y.coeff 0) := by
  first | exact @GlobalTheory.wittVector_eq_teichmuller_of_frobenius_eq_pow | exact GlobalTheory.wittVector_eq_teichmuller_of_frobenius_eq_pow | (intros; apply GlobalTheory.wittVector_eq_teichmuller_of_frobenius_eq_pow <;> assumption)
