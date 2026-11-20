import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizedLatticeFiniteProjective
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
open TensorProduct GlobalTheory.PerfdLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.localizedModule_finite_projective_of_smul_mem` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalizedLatticeFiniteProjective.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.localized_lattice_finite_projective : ∀ (A : Type) [CommRing A] (f : A) (h : ℕ) (L : Submodule A (Fin h → A)), (∀ x : Fin h → A, f • x ∈ L) → Module.Finite (Localization.Away f) (LocalizedModule (Submonoid.powers f) L) ∧ Module.Projective (Localization.Away f) (LocalizedModule (Submonoid.powers f) L) := by
  first | exact @GlobalTheory.localizedModule_finite_projective_of_smul_mem | exact GlobalTheory.localizedModule_finite_projective_of_smul_mem | (intros; apply GlobalTheory.localizedModule_finite_projective_of_smul_mem <;> assumption)
