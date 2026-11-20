import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowDescentCyclotomic
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_pow_descent_cyclotomic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsPowDescentCyclotomic.lean&line=141#L141)
-/
theorem _root_.GlobalTheory.T.exists_pow_descent_cyclotomic' : ∀ (E : Type) [Field E] [NumberField E] (l r : ℕ), l.Prime → ∃ M : ℕ, 0 < M ∧ l ^ r ∣ M ∧
    ∀ (Ω : Type) [Field Ω] [Algebra E Ω] (ζ : Ω), IsPrimitiveRoot ζ M → ∀ (u : E) (w : Ω),
      w ∈ IntermediateField.adjoin E {ζ} → w ^ M = algebraMap E Ω u → ∃ v : E, v ^ (l ^ r) = u := by
  first | exact @GlobalTheory.exists_pow_descent_cyclotomic | exact GlobalTheory.exists_pow_descent_cyclotomic | (intros; apply GlobalTheory.exists_pow_descent_cyclotomic <;> assumption)
