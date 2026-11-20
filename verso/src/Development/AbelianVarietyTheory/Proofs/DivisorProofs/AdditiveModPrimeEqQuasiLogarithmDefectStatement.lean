import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveModPrimeEqQuasiLogarithmDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdditiveModPrimeEqQuasiLogarithmDefect.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.additive_mod_prime_eq_quasiLogarithm_defect : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (b : G.A 1) (z : G.A 1 ⊗[O] G.A 1), cobOne O (G.A 1) b = (p : O) • z → ∃ (f : MvPowerSeries (Fin d) E) (s : MvPowerSeries (Fin d) O) (y : G.A 1), QL c.μ ⊤ f ∧ map (algebraMap O E) s = defect c.μ p f ∧ c.ev 1 s = b + (p : O) • y := by
  first | exact @GlobalTheory.QLog.additive_mod_p_is_defect | exact GlobalTheory.QLog.additive_mod_p_is_defect | (intros; apply GlobalTheory.QLog.additive_mod_p_is_defect <;> assumption)
