import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSurjectiveValuationIsIntegralIffNonneg
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsSurjectiveValuationIsIntegralIffNonneg.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_surjective_valuation_isIntegral_iff_nonneg : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.E L] [Algebra K.O L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], ∃ v : Lˣ →* Multiplicative ℤ, Function.Surjective v ∧ ∀ x : Lˣ, IsIntegral K.O (x : L) ↔ 0 ≤ Multiplicative.toAdd (v x) := by
  first | exact @GlobalTheory.UnitLemma.exists_surjective_valuation_isIntegral_iff | exact GlobalTheory.UnitLemma.exists_surjective_valuation_isIntegral_iff | (intros; apply GlobalTheory.UnitLemma.exists_surjective_valuation_isIntegral_iff <;> assumption)
