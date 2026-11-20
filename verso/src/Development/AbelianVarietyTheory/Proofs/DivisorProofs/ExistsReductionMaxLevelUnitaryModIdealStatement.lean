import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReductionMaxLevelUnitaryModIdeal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open GlobalTheory.FunObj.SqNum GlobalTheory.NormSum

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsReductionMaxLevelUnitaryModIdeal.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.exists_reduction_maxLevel_unitary_mod_ideal : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ N : ℕ,
    ∃ ρ : ↥(intG D N) →* GL (Fin N) (𝓞 D.host.E ⧸ 𝔪), ∀ (k : ↥(intG D N)) (i j : Fin N) (b : 𝓞 D.host.E),
      ((ρ k : Matrix (Fin N) (Fin N) (𝓞 D.host.E ⧸ 𝔪)) i j = Ideal.Quotient.mk 𝔪 b ↔
        (((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j - inc D (b : D.host.E) ∈ hatId D 𝔪) := by
  first | exact @GlobalTheory.LevelRed.exists_levelRed | exact GlobalTheory.LevelRed.exists_levelRed | (intros; apply GlobalTheory.LevelRed.exists_levelRed <;> assumption)
