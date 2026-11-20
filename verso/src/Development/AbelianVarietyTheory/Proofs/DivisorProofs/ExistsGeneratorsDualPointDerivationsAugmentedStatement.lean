import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorsDualPointDerivationsAugmented
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_generators_dual_point_derivations` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsGeneratorsDualPointDerivationsAugmented.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_generators_dual_point_derivations_augmented : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k), IsNilpotent (RingHom.ker ε) → ∃ (d : ℕ) (x : Fin d → A) (l : Fin d → A →ₗ[k] k), (∀ i a b, l i (a * b) = ε a * l i b + ε b * l i a) ∧ (∀ i j, l i (x j) = if i = j then 1 else 0) ∧ Algebra.adjoin k (Set.range x) = ⊤ := by
  first | exact @GlobalTheory.exists_generators_dual_point_derivations | exact GlobalTheory.exists_generators_dual_point_derivations | (intros; apply GlobalTheory.exists_generators_dual_point_derivations <;> assumption)
