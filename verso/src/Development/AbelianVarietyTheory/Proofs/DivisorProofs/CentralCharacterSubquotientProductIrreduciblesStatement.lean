import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralCharacterSubquotientProductIrreducibles
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCentralCharacterSubquotientProductIrreducibles.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.centralCharacter_subquotient_productIrreducibles : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ x : IrrGL k, ∃ ω : kˣ →* ℂˣ, HasCentralChar x.rep ω) ∧ ∀ (t m : ℕ) (x : Fin t → IrrGL k) (hd : ∑ a, (x a).1 = m) (ω : Fin t → kˣ →* ℂˣ), (∀ a, HasCentralChar (x a).rep (ω a)) → ∀ (τ : IrrRep (GL (Fin m) k)) (ω' : kˣ →* ℂˣ), IsSubquotient τ.ρ (prodIrr x hd) → HasCentralChar τ.ρ ω' → ω' = ∏ a, ω a := by
  first | exact @GlobalTheory.GamMul.centralChar_subquotient_prodIrr | exact GlobalTheory.GamMul.centralChar_subquotient_prodIrr | (intros; apply GlobalTheory.GamMul.centralChar_subquotient_prodIrr <;> assumption)
