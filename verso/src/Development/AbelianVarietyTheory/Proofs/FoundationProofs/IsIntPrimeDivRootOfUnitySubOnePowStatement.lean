import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntPrimeDivRootOfUnitySubOnePow
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.K5.PDiv.pdiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FIsIntPrimeDivRootOfUnitySubOnePow.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (j s : ℕ), 1 ≤ j → s ≤ Nat.totient (p ^ j) → IsInt p ((p : Ω) / (T.ζ j - 1) ^ s) := by
  first | exact @GlobalTheory.K5.PDiv.pdiv | exact GlobalTheory.K5.PDiv.pdiv | (intros; apply GlobalTheory.K5.PDiv.pdiv <;> assumption)
