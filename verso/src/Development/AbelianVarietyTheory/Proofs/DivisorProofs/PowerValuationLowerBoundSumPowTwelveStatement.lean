import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerValuationLowerBoundSumPowTwelve
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.LatValSum.valGe_sum_pow_twelve | exact GlobalTheory.LatValSum.valGe_sum_pow_twelve | (intros; apply GlobalTheory.LatValSum.valGe_sum_pow_twelve <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.powerValuationLowerBound_sum_pow_twelve : ∀ (l : ℕ), l.Prime → ∀ (r : ℝ) (J : Type) [Fintype J] (u x : J → ℂ), (∀ j, IntAt l (u j)) → (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r (x j ^ 12)) → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r ((∑ j, u j * x j) ^ 12) := by
  first | exact @GlobalTheory.LatValSum.valGe_sum_pow_twelve | exact GlobalTheory.LatValSum.valGe_sum_pow_twelve | (intros; apply GlobalTheory.LatValSum.valGe_sum_pow_twelve <;> assumption)
