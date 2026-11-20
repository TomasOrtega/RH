import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzVanishingDecomposition
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzVanishingDecomposition.lean&line=115#L115)
-/
theorem _root_.GlobalTheory.T.schwartz_vanishing_decomposition : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ), f 0 = 0 → ∃ (n : ℕ) (L : Fin n → V →L[ℝ] ℝ) (h g : Fin n → SchwartzMap V ℂ),
      (∀ i x, g i x = (L i x : ℂ) * h i x) ∧ ∀ x, f x = ∑ i, g i x := by
  first | exact @GlobalTheory.SchwartzDiv.hadamard | exact GlobalTheory.SchwartzDiv.hadamard | (intros; apply GlobalTheory.SchwartzDiv.hadamard <;> assumption)
