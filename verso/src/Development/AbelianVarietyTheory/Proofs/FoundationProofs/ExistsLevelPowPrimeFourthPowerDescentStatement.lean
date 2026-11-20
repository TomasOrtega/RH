import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelPowPrimeFourthPowerDescent
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.ES.desc_pow_four` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsLevelPowPrimeFourthPowerDescent.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.exists_level_pow_prime_fourth_power_descent : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l n M : ℕ), l.Prime → 0 < M → 6 * l ∣ M → ∀ f : X.Kˣ, (∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ, X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) → ∃ (k : ℕ) (h : X.Kˣ), Lev X (M * l ^ k) ((f : X.K) ^ 4 * (h : X.K) ^ (l ^ n)) := by
  first | exact @GlobalTheory.KZ.ES.desc_pow_four | exact GlobalTheory.KZ.ES.desc_pow_four | (intros; apply GlobalTheory.KZ.ES.desc_pow_four <;> assumption)
