import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCountLogConcavePrimePowers
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.card_torsion_pow_log_concave` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTorsionCountLogConcavePrimePowers.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.torsion_count_log_concave_prime_powers : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (𝔭 : Ideal (𝓞 F)), 𝔭.IsMaximal → ∀ k : ℕ,
    Finite {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} →
    Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} * Nat.card {x : M // ∀ a ∈ 𝔭 ^ k, a • x = 0} ≤
      Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 1), a • x = 0} ^ 2 := by
  first | exact @GlobalTheory.card_torsion_pow_log_concave | exact GlobalTheory.card_torsion_pow_log_concave | (intros; apply GlobalTheory.card_torsion_pow_log_concave <;> assumption)
