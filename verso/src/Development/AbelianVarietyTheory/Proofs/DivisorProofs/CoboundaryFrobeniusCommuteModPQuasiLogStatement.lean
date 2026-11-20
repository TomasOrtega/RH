import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryFrobeniusCommuteModPQuasiLog
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrobCongr.frob_cong` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoboundaryFrobeniusCommuteModPQuasiLog.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.coboundary_frobenius_commute_mod_p_quasiLog : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (F : BFrame ε) (d : ℕ) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) F.Q), (∀ i, QL μ' ⊤ (e i)) → ∀ b : ι → F.B, In (Ideal.span {(p : F.B)}) (cob1 (up F.Q μ') (frob p F.s (comb b e)) - frob p F.s (cob1 (up F.Q μ') (comb b e))) := by
  first | exact @GlobalTheory.FrobCongr.frob_cong | exact GlobalTheory.FrobCongr.frob_cong | (intros; apply GlobalTheory.FrobCongr.frob_cong <;> assumption)
