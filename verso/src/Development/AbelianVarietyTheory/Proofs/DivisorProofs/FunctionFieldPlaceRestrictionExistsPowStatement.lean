import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceRestrictionExistsPow
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Nef.place_res_exists_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFunctionFieldPlaceRestrictionExistsPow.lean&line=149#L149)
-/
theorem _root_.GlobalTheory.T.functionFieldPlace_restriction_exists_pow : ∀ (k F E : Type) [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], (∃ ρ : Place k E → Place k F, IsRes ρ) ∧ ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ p, ∃ e : ℕ, 0 < e ∧ (∀ x : F, p.1 (algebraMap F E x) = (ρ p).1 x ^ e) ∧ ∀ x : F, ord p (algebraMap F E x) = e * ord (ρ p) x := by
  first | exact @GlobalTheory.Nef.place_res_exists_pow | exact GlobalTheory.Nef.place_res_exists_pow | (intros; apply GlobalTheory.Nef.place_res_exists_pow <;> assumption)
