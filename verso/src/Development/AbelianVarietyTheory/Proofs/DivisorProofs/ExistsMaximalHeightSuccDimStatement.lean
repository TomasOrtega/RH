import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalHeightSuccDim
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FibreMax.exists_isMaximal_height_ge` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsMaximalHeightSuccDim.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_maximal_height_succ_dim : ∀ (k : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k] [CharZero k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [FaithfulSMul k A] (d : ℕ), ringKrullDim (FractionRing k ⊗[k] A) = d → ∃ M : Ideal A, M.IsMaximal ∧ ((d + 1 : ℕ) : ℕ∞) ≤ M.height := by
  first | exact @GlobalTheory.FibreMax.exists_isMaximal_height_ge | exact GlobalTheory.FibreMax.exists_isMaximal_height_ge | (intros; apply GlobalTheory.FibreMax.exists_isMaximal_height_ge <;> assumption)
