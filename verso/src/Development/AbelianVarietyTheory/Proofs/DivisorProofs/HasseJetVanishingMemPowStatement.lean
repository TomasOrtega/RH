import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasseJetVanishingMemPow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQuotBijective
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.hasseJet_vanishing_mem_pow` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHasseJetVanishingMemPow.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_maximal_mem_pow_of_hasse_vanishing : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (Δ : ℕ → A →ₗ[k] k), 2 ≤ N → Δ 0 1 = 1 → (∀ l < N, ∀ u w : A, Δ l (u * w) = ∑ p ∈ Finset.range (l + 1), Δ p u * Δ (l - p) w) → (∃ π : A, Δ 1 π = 1) → ∃ Q : Ideal A, Q.IsMaximal ∧ (∀ u, u ∈ Q ↔ Δ 0 u = 0) ∧ ∀ f : A, (∀ l < N, Δ l f = 0) → f ∈ Q ^ N := by
  first | exact @GlobalTheory.hasseJet_vanishing_mem_pow | exact GlobalTheory.hasseJet_vanishing_mem_pow | (intros; apply GlobalTheory.hasseJet_vanishing_mem_pow <;> assumption)
