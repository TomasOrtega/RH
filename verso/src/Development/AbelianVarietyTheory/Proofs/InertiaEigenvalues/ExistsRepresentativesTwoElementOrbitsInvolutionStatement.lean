import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepresentativesTwoElementOrbitsInvolution
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.involution_pair_representatives` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsRepresentativesTwoElementOrbitsInvolution.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.exists_representatives_two_element_orbits_involution : ∀ (ι : Type) [Finite ι] (s : ι → ι), (∀ i, s (s i) = i) → ∃ (r : ℕ) (e : Fin r → ι), (∀ j k, e j = e k → j = k) ∧ (∀ j k, s (e j) ≠ e k) ∧ ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j) := by
  first | exact @GlobalTheory.involution_pair_representatives | exact GlobalTheory.involution_pair_representatives | (intros; apply GlobalTheory.involution_pair_representatives <;> assumption)
