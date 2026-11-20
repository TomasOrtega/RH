import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TranslateCoprimeOrderNotIncreaseThetaCombNorm
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MomOne.TranslNorm.translate_bd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FTranslateCoprimeOrderNotIncreaseThetaCombNorm.lean&line=114#L114)
-/
theorem _root_.GlobalTheory.T.translate_coprime_order_not_increase_theta_comb_norm : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (a m : ℕ) (c : Fin m → ℂ_[q]) (s : Fin m → ℂ) (t : ℂ) (B : ℝ), (∀ j, PrimeTo d q (s j)) → PrimeTo d q t → ¬ InOK d (t - 1 / 2) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d (s j) θ) ^ a) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d t (U1 d (s j) θ)) ^ a) := by
  first | exact @GlobalTheory.MomOne.TranslNorm.translate_bd | exact GlobalTheory.MomOne.TranslNorm.translate_bd | (intros; apply GlobalTheory.MomOne.TranslNorm.translate_bd <;> assumption)
