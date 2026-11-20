import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem fsLog_pointOf_le_log_norm : ∀ (n : ℕ) (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)), y ≠ 0 →
  ∑ j, u j * h.pointOf y j ≠ 0 → fsLog h u (h.pointOf y) ≤ Real.log (h.norm u) :=
  fun _ h _ _ _ hne => fsLog_le h hne

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
