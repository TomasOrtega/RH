import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSingleDerivationTaylorPowerSeries
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FormalOrigin.Extend.taylor_coeff_single` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoeffSingleDerivationTaylorPowerSeries.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.coeff_single_derivationTaylorPowerSeries : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A) (j : Fin n) (f : A), MvPowerSeries.coeff (Finsupp.single j 1) (taylor ev (fun i => ⇑(ds i)) f) = ev (ds j f) := by
  first | exact @GlobalTheory.FormalOrigin.Extend.taylor_coeff_single | exact GlobalTheory.FormalOrigin.Extend.taylor_coeff_single | (intros; apply GlobalTheory.FormalOrigin.Extend.taylor_coeff_single <;> assumption)
