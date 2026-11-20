import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisRealBasisOfHolomorphicFamily
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
open GlobalTheory.ShFam.Hor.LogCh

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeBasisRealBasisOfHolomorphicFamily.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.latticeBasis_realBasis_of_holomorphic_family : ∀ (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (b₀ : Fin n → ℂ) (lam : Fin r → Fin g → ℂ), IsLatFam B K → b₀ ∈ B → Submodule.span ℝ (K b₀) = ⊤ → LinearIndependent ℤ lam → (∀ w, w ∈ K b₀ ↔ ∃ k : Fin r → ℤ, w = ∑ j, k j • lam j) → LinearIndependent ℝ lam ∧ Submodule.span ℝ (Set.range lam) = ⊤ := by
  first | exact @GlobalTheory.LatReal.isRealBasis_of_isLatFam | exact GlobalTheory.LatReal.isRealBasis_of_isLatFam | (intros; apply GlobalTheory.LatReal.isRealBasis_of_isLatFam <;> assumption)
