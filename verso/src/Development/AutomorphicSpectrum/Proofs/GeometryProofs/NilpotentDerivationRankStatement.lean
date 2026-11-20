import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NilpotentDerivationRank
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FNilpotentDerivationRank.lean&line=173#L173)
-/
theorem _root_.GlobalTheory.T.nilpotent_derivation_rank : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R] (D : Derivation k R R) (ε : R →ₐ[k] k),
    (∀ a : R, (⇑D)^[p] a = 0) → ∀ t : R, IsUnit ((⇑D)^[p - 1] t) →
      Module.finrank k R = p * Module.finrank k (LinearMap.ker (D : R →ₗ[k] R)) ∧
      ∃ z : R, ε (D z) ≠ 0 ∧ ∀ u : R →ₗ[k] k, (∀ a b : R, u (a * b) = u a * ε b + ε a * u b) →
        (∀ a : R, D a = 0 → u a = 0) → u z = 0 → u = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.DerivFree.finrank_and_vanishing | exact GlobalTheory.CompanionTheory.Ggeo.DerivFree.finrank_and_vanishing | (intros; apply GlobalTheory.CompanionTheory.Ggeo.DerivFree.finrank_and_vanishing <;> assumption)
