import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusSurjectiveModPrimeCyclotomicKummerTower
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.K5.frob_surj_adjoin_tower` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FFrobeniusSurjectiveModPrimeCyclotomicKummerTower.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.frobenius_surjective_mod_prime_cyclotomicKummerTower : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω), ∀ x ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ y ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ z ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), x = y ^ p + (p : Ω) * z := by
  first | exact @GlobalTheory.K5.frob_surj_adjoin_tower | exact GlobalTheory.K5.frob_surj_adjoin_tower | (intros; apply GlobalTheory.K5.frob_surj_adjoin_tower <;> assumption)
