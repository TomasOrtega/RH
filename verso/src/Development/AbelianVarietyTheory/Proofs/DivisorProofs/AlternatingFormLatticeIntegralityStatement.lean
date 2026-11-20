import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingFormLatticeIntegrality
import Mathlib
open NumberField
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_alternating_bilinForm_eq_pairing` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAlternatingFormLatticeIntegrality.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.alternating_form_lattice_integrality : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (L : Set V),
    (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) → ∀ (P : V → V → F),
    (∀ x ∈ L, ∀ x' ∈ L, P x x' = -P x' x) →
    (∀ x₁ ∈ L, ∀ x₂ ∈ L, ∀ x' ∈ L, P (x₁ + x₂) x' = P x₁ x' + P x₂ x') →
    (∀ (a : 𝓞 F), ∀ x ∈ L, ∀ x' ∈ L, P ((a : F) • x) x' = (a : F) * P x x') →
    ∀ {x x' : V}, x ∈ L → x' ∈ L → P x x' ≠ 0 →
    ∃ B : LinearMap.BilinForm F V, (∀ z, B z z = 0) ∧ ∀ z ∈ L, ∀ w ∈ L, P z w = B z w := by
  first | exact @GlobalTheory.exists_alternating_bilinForm_eq_pairing | exact GlobalTheory.exists_alternating_bilinForm_eq_pairing | (intros; apply GlobalTheory.exists_alternating_bilinForm_eq_pairing <;> assumption)
