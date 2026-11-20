import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumberFieldToModPSquared
open scoped TensorProduct Polynomial
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNumberFieldToModPSquared.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.number_field_to_mod_p_squared : ∀ (K : Type) [Field K] [NumberField K] (S : Finset K) (n : ℕ), ∃ p : ℕ, p.Prime ∧ n < p ∧ Nonempty (Subring.closure (S : Set K) →+* ZMod (p ^ 2)) := by
  first | exact @_root_.GlobalTheory.exists_prime_sq_ringHom_of_closure | exact _root_.GlobalTheory.exists_prime_sq_ringHom_of_closure | (intros; apply _root_.GlobalTheory.exists_prime_sq_ringHom_of_closure <;> assumption)
