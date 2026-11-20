import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationCentralCharacterIsolate
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
open GlobalTheory.PRep GlobalTheory.SmGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiltrationCentralCharacterIsolate.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.filtration_central_character_isolate : ∀ {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G X) (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ),
    Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ → ∀ (z : G), (∀ g, g * z = z * g) → ∀ (t₀ : Fin N) (a : ℂ),
    Nonempty ((subQuot (S t₀.succ) (S t₀.castSucc)).Equiv σ) → (∀ y, σ z y = a • y) →
    (∀ t, t ≠ t₀ → ∃ q : Polynomial ℂ, q.eval a ≠ 0 ∧
      ∀ w ∈ (S t.succ).toSubmodule, Polynomial.aeval (ρ z) q w ∈ (S t.castSucc).toSubmodule) →
    ∃ p : ρ.IntertwiningMap σ, (∀ y, ∃ v, ρ z v = a • v ∧ p v = y) ∧
      ∀ v, ρ z v = a • v → p v = 0 → v = 0 := by
  first | exact @GlobalTheory.exists_intertwining_bijOn_eigen_of_central_step | exact GlobalTheory.exists_intertwining_bijOn_eigen_of_central_step | (intros; apply GlobalTheory.exists_intertwining_bijOn_eigen_of_central_step <;> assumption)
