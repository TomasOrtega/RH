import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFrobeniusLiftSmulLogCoordinateWedge
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
open GlobalTheory GlobalTheory.LogDR

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLogFrobeniusLiftSmulLogCoordinateWedge.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.logFrobeniusLift_smul_logCoordinateWedge : ∀ (K : Type) [Field K] (p : ℕ) (n : ℕ) (x : Fin n → Kˣ) (γ : abelian₂ K →+* abelian₂ K), IsCartierMap p x γ → ∀ (c : K) (I : Finset (Fin n)), γ (c • logWedge x I) = c ^ p • logWedge x I := by
  first | exact @GlobalTheory.cartierMap_smul_logWedge | exact GlobalTheory.cartierMap_smul_logWedge | (intros; apply GlobalTheory.cartierMap_smul_logWedge <;> assumption)
