import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftingResidueValues
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtChart
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DenseSec.hensel_etChart` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSectionLiftingResidueValues.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.exists_section_lifting_residue_values : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (ε : A →ₐ[R] R), IsUnit (ε h) → ∀ c : Fin g → R, (∀ i, c i - ε (t i) ∈ maximalIdeal R) → ∃ a : A →ₐ[R] R, IsUnit (a h) ∧ ∀ i, a (t i) = c i := by
  first | exact @GlobalTheory.DenseSec.hensel_etChart | exact GlobalTheory.DenseSec.hensel_etChart | (intros; apply GlobalTheory.DenseSec.hensel_etChart <;> assumption)
