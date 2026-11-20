import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotPowMaximalCharPLocalCard
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.quot_pow_maximal_charP_local_card` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FQuotPowMaximalCharPLocalCard.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.quotient_pow_finite_uniformizer_card_eq : ∀ (L : Type) [Field L] [NumberField L] (la J : Ideal (𝓞 L)) [la.IsMaximal] (l e b : ℕ), l.Prime → 0 < e → 0 < b → la ⊔ J = ⊤ → Ideal.span {((l : ℕ) : 𝓞 L)} = la ^ e * J → CharP (𝓞 L ⧸ la ^ (e * b)) (l ^ b) ∧ Finite (𝓞 L ⧸ la ^ (e * b)) ∧ ∃ π : 𝓞 L ⧸ la ^ (e * b), (∀ x : 𝓞 L ⧸ la ^ (e * b), ¬ IsUnit x ↔ π ∣ x) ∧ Ideal.span {((l : ℕ) : 𝓞 L ⧸ la ^ (e * b))} = Ideal.span {π ^ e} ∧ Nat.card (𝓞 L ⧸ la ^ (e * b)) = Nat.card ((𝓞 L ⧸ la ^ (e * b)) ⧸ Ideal.span {π}) ^ (b * e) := by
  first | exact @GlobalTheory.quot_pow_maximal_charP_local_card | exact GlobalTheory.quot_pow_maximal_charP_local_card | (intros; apply GlobalTheory.quot_pow_maximal_charP_local_card <;> assumption)
