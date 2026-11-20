import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationDividedPowerFiltrationSuccLe
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDerivationDividedPowerFiltrationSuccLe.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.derivation_dividedPowerFiltration_succ_le : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module R M] [IsScalarTower R B M] (J : Ideal B) (δ : DividedPowers J) (D : Derivation R B M) (N₀ : Submodule B M), (∀ n, ∀ a ∈ J, D (δ.dpow (n + 1) a) - δ.dpow n a • D a ∈ N₀) → ∀ N, ∀ x ∈ fil δ (N + 1), D x ∈ fil δ N • (⊤ : Submodule B M) ⊔ N₀ := by
  first | exact @GlobalTheory.DerFil.deriv_fil_succ_le | exact GlobalTheory.DerFil.deriv_fil_succ_le | (intros; apply GlobalTheory.DerFil.deriv_fil_succ_le <;> assumption)
